import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Lean.Util.CollectAxioms

/-! A convergent function with Lipschitz derivative has derivative tending
to zero. This supplies the endpoint argument for translator rigidity. -/
noncomputable section
open Set Filter
open scoped Topology
namespace OpenTranslator

theorem derivative_le_difference_quotient {f g : ℝ → ℝ} {C : ℝ}
    (hd : ∀ x, HasDerivAt f (g x) x) (hC : 0 ≤ C)
    (hLip : ∀ x y, |g x-g y| ≤ C*|x-y|) (x : ℝ) {h : ℝ} (hh : 0<h) :
    |g x| ≤ |(f (x+h)-f x)/h| + C*h := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  obtain ⟨c, hc, hgc⟩ := exists_hasDerivAt_eq_slope f g
    (show x<x+h by linarith) hfc.continuousOn (fun u _ => hd u)
  have hdiff : |g x-g c| ≤ C*h := by
    apply (hLip x c).trans
    apply mul_le_mul_of_nonneg_left _ hC
    rw [abs_of_neg (by linarith [hc.1] : x-c<0)]
    linarith [hc.2]
  have he : x+h-x=h := by ring
  rw [he] at hgc
  calc
    |g x| = |(g x-g c)+g c| := by congr 1; ring
    _ ≤ |g x-g c|+|g c| := abs_add_le _ _
    _ ≤ C*h+|g c| := add_le_add hdiff le_rfl
    _ = C*h+|(f (x+h)-f x)/h| := by rw [hgc]
    _ = _ := add_comm _ _

theorem derivative_tendsto_zero_atTop {f g : ℝ → ℝ} {C l : ℝ}
    (hd : ∀ x, HasDerivAt f (g x) x) (hC : 0 ≤ C)
    (hLip : ∀ x y, |g x-g y| ≤ C*|x-y|)
    (hf : Tendsto f atTop (𝓝 l)) : Tendsto g atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let h : ℝ := ε/(2*(C+1))
  have hh : 0<h := by dsimp [h]; positivity
  have heq : 2*(C+1)*h=ε := by dsimp [h]; field_simp
  have hCh : C*h ≤ ε/2 := by nlinarith
  have hshift : Tendsto (fun x : ℝ => x+h) atTop atTop :=
    tendsto_atTop_add_const_right atTop h tendsto_id
  have hq : Tendsto (fun x => |(f (x+h)-f x)/h|) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, zero_div, abs_zero] using (((hf.comp hshift).sub hf).div_const h).abs
  have hev : ∀ᶠ x in atTop, |(f (x+h)-f x)/h| < ε/2 :=
    (tendsto_order.mp hq).2 (ε/2) (by positivity)
  filter_upwards [hev] with x hx
  rw [Real.dist_eq, sub_zero]
  have hb := derivative_le_difference_quotient hd hC hLip x hh
  linarith

theorem derivative_tendsto_zero_atBot {f g : ℝ → ℝ} {C l : ℝ}
    (hd : ∀ x, HasDerivAt f (g x) x) (hC : 0 ≤ C)
    (hLip : ∀ x y, |g x-g y| ≤ C*|x-y|)
    (hf : Tendsto f atBot (𝓝 l)) : Tendsto g atBot (𝓝 0) := by
  have hdrev : ∀ x, HasDerivAt (fun u => f (-u)) (-g (-x)) x := by
    intro x
    simpa only [Function.comp_def, id_eq, mul_neg, mul_one] using
      (hd (-x)).comp x (hasDerivAt_id x).neg
  have hLrev : ∀ x y, |-g (-x)-(-g (-y))| ≤ C*|x-y| := by
    intro x y
    calc
      |-g (-x)-(-g (-y))| = |g (-x)-g (-y)| := by
        rw [show -g (-x)-(-g (-y)) = -(g (-x)-g (-y)) by ring, abs_neg]
      _ ≤ C*|(-x)-(-y)| := hLip (-x) (-y)
      _ = C*|x-y| := by
        rw [show (-x)-(-y) = -(x-y) by ring, abs_neg]
  have hr := derivative_tendsto_zero_atTop hdrev hC hLrev
    (hf.comp tendsto_neg_atTop_atBot)
  have hb := hr.comp tendsto_neg_atBot_atTop
  simpa only [Function.comp_def, neg_neg, neg_zero] using hb.neg

end OpenTranslator

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`OpenTranslator).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext, `Classical.choice, `Quot.sound] : Array Name).contains axiomName do
          throwError "Derivative limit audit failed: {name} depends on {axiomName}"
  logInfo "Derivative limit audit passed; standard axioms only."
