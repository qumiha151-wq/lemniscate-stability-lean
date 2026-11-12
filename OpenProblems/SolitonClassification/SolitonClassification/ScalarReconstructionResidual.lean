import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms

/-! Actual scalar curvature and the globally defined candidate support.
The identities proved here are preparation for continuation across zeros.
Global vanishing of the defect is not assumed or claimed by this module. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff
namespace ClosedSimilarity.ScalarReconstruction

def force (k : ℝ → ℝ) (s : ℝ) : ℝ := deriv (deriv k) s + k s^3/2
def numerator (k : ℝ → ℝ) (b s : ℝ) : ℝ := deriv (force k) s+b
def supportDerivative (k : ℝ → ℝ) (a s : ℝ) : ℝ := a-k s*force k s
def candidateSupport (k : ℝ → ℝ) (a b s₀ s : ℝ) : ℝ :=
  numerator k b s₀/k s₀ + ∫ u in s₀..s, supportDerivative k a u
def defect (k : ℝ → ℝ) (a b s₀ s : ℝ) : ℝ :=
  numerator k b s-k s*candidateSupport k a b s₀ s

/-- The actual degenerate fourth-order equation, with all derivatives
computed from the same curvature function. -/
def ScalarEquation (k : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ s, k s*deriv (deriv (force k)) s-deriv k s*numerator k b s =
    k s^2*supportDerivative k a s

theorem force_smooth {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) :
    ContDiff ℝ ∞ (force k) := by
  have hk₁ := (contDiff_infty_iff_deriv.mp hk).2
  have hk₂ := (contDiff_infty_iff_deriv.mp hk₁).2
  exact hk₂.add ((hk.pow 3).div_const 2)

theorem numerator_smooth {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) (b : ℝ) :
    ContDiff ℝ ∞ (numerator k b) :=
  ((contDiff_infty_iff_deriv.mp (force_smooth hk)).2).add contDiff_const

theorem supportDerivative_smooth {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) (a : ℝ) :
    ContDiff ℝ ∞ (supportDerivative k a) :=
  contDiff_const.sub (hk.mul (force_smooth hk))

theorem candidateSupport_hasDerivAt {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    (a b s₀ s : ℝ) :
    HasDerivAt (candidateSupport k a b s₀) (supportDerivative k a s) s := by
  have hg := (supportDerivative_smooth hk a).continuous
  exact (intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable s₀ s)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt).const_add _

theorem candidateSupport_smooth {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    (a b s₀ : ℝ) : ContDiff ℝ ∞ (candidateSupport k a b s₀) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun s => (candidateSupport_hasDerivAt hk a b s₀ s).differentiableAt, ?_⟩
  have he : deriv (candidateSupport k a b s₀)=supportDerivative k a :=
    funext fun s => (candidateSupport_hasDerivAt hk a b s₀ s).deriv
  rw [he]
  exact supportDerivative_smooth hk a

theorem defect_smooth {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) (a b s₀ : ℝ) :
    ContDiff ℝ ∞ (defect k a b s₀) :=
  (numerator_smooth hk b).sub (hk.mul (candidateSupport_smooth hk a b s₀))

theorem numerator_hasDerivAt {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) (b s : ℝ) :
    HasDerivAt (numerator k b) (deriv (deriv (force k)) s) s := by
  have hf₁ := (contDiff_infty_iff_deriv.mp (force_smooth hk)).2
  exact (hf₁.differentiable (by simp) s).hasDerivAt.add_const b

theorem defect_hasDerivAt {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    (a b s₀ s : ℝ) :
    HasDerivAt (defect k a b s₀)
      (deriv (deriv (force k)) s-
        (deriv k s*candidateSupport k a b s₀ s+k s*supportDerivative k a s)) s :=
  (numerator_hasDerivAt hk b s).sub
    ((hk.differentiable (by simp) s).hasDerivAt.mul (candidateSupport_hasDerivAt hk a b s₀ s))

theorem defect_at_anchor (k : ℝ → ℝ) (a b s₀ : ℝ) (hne : k s₀ ≠ 0) :
    defect k a b s₀ s₀=0 := by
  simp only [defect,candidateSupport,intervalIntegral.integral_same,add_zero]
  field_simp
  ring

theorem defect_wronskian {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    {a b : ℝ} (hS : ScalarEquation k a b) (s₀ s : ℝ) :
    k s*deriv (defect k a b s₀) s-deriv k s*defect k a b s₀ s=0 := by
  rw [(defect_hasDerivAt hk a b s₀ s).deriv]
  dsimp only [defect]
  have he := hS s
  calc
    _ = (k s*deriv (deriv (force k)) s-deriv k s*numerator k b s)-
        k s^2*supportDerivative k a s := by ring
    _ = 0 := by rw [he]; ring

theorem defect_quotient_hasDerivAt {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    {a b : ℝ} (hS : ScalarEquation k a b) (s₀ s : ℝ) (hne : k s ≠ 0) :
    HasDerivAt (fun u => defect k a b s₀ u/k u) 0 s := by
  have hd := ((defect_smooth hk a b s₀).differentiable (by simp) s).hasDerivAt.fun_div
    (hk.differentiable (by simp) s).hasDerivAt hne
  have hz : deriv (defect k a b s₀) s*k s-defect k a b s₀ s*deriv k s=0 := by
    convert defect_wronskian hk hS s₀ s using 1
    ring
  simpa only [hz,zero_div] using hd

/-- Actual equality on every interval from the anchor containing no zero of k.
The continuation through zeros is a separate remaining argument. -/
theorem candidateSupport_eq_quotient_on_interval {k : ℝ → ℝ}
    (hk : ContDiff ℝ ∞ k) {a b : ℝ} (hS : ScalarEquation k a b)
    (s₀ s : ℝ) (hne : ∀ u ∈ uIcc s₀ s, k u ≠ 0) :
    numerator k b s=k s*candidateSupport k a b s₀ s := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => defect_quotient_hasDerivAt hk hS s₀ u (hne u hu))
    (intervalIntegrable_const (a := s₀) (b := s) (c := (0:ℝ)))
  have hs₀ := hne s₀ (left_mem_uIcc)
  rw [intervalIntegral.integral_zero,defect_at_anchor k a b s₀ hs₀,zero_div,sub_zero] at hi
  have hz : defect k a b s₀ s=0 := (div_eq_zero_iff).mp hi.symm |>.resolve_right (hne s right_mem_uIcc)
  exact sub_eq_zero.mp hz

theorem candidateSupport_unique {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    (a b s₀ : ℝ) (hne : k s₀ ≠ 0) (H : ℝ → ℝ)
    (hH : ∀ s, HasDerivAt H (supportDerivative k a s) s)
    (hanchor : numerator k b s₀=k s₀*H s₀) :
    H=candidateSupport k a b s₀ := by
  funext s
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hH u) ((supportDerivative_smooth hk a).continuous.intervalIntegrable s₀ s)
  have hv : numerator k b s₀/k s₀=H s₀ := by rw [hanchor]; field_simp
  dsimp only [candidateSupport]
  rw [hv,hi]
  ring

theorem candidateSupport_eq_quotient_of_ne_zero {k : ℝ → ℝ}
    (hk : ContDiff ℝ ∞ k) {a b : ℝ} (hS : ScalarEquation k a b)
    (hne : ∀ s, k s ≠ 0) (s₀ s : ℝ) :
    numerator k b s=k s*candidateSupport k a b s₀ s :=
  candidateSupport_eq_quotient_on_interval hk hS s₀ s (fun u _ => hne u)

end ClosedSimilarity.ScalarReconstruction

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`ClosedSimilarity).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Scalar reconstruction audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Scalar reconstruction residual audit passed for {count} declarations."
