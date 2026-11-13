import LengthGrowth.ScalarDissipation
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Conditional scalar decay under fifth-power coercivity. The energy law
and coercivity are explicit scalar premises here; the actual-flow adapter
must discharge them from the normal PDE and a bound on absolute curvature.
Differentiation is used only at strictly positive times. -/

noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

namespace FreeElasticScalar

def fourthRoot (x : ℝ) : ℝ := Real.sqrt (Real.sqrt x)

theorem fourthRoot_nonneg (x : ℝ) : 0 ≤ fourthRoot x := Real.sqrt_nonneg _

theorem fourthRoot_pos {x : ℝ} (hx : 0 < x) : 0 < fourthRoot x :=
  Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hx)

theorem fourthRoot_sq (x : ℝ) : fourthRoot x ^ 2 = Real.sqrt x :=
  Real.sq_sqrt (Real.sqrt_nonneg x)

theorem fourthRoot_pow_four {x : ℝ} (hx : 0 ≤ x) : fourthRoot x ^ 4 = x := by
  calc
    fourthRoot x ^ 4 = (fourthRoot x ^ 2) ^ 2 := by ring
    _ = Real.sqrt x ^ 2 := by rw [fourthRoot_sq]
    _ = x := Real.sq_sqrt hx

theorem fourthRoot_continuous : Continuous fourthRoot :=
  Real.continuous_sqrt.comp Real.continuous_sqrt

theorem fourthRoot_mono : Monotone fourthRoot :=
  fun _ _ h => Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h)

theorem inverse_fourth_hasDerivAt {E : ℝ → ℝ} {D x : ℝ}
    (hE : E x ≠ 0) (hd : HasDerivAt E (-D) x) :
    HasDerivAt (fun s => (E s)⁻¹ ^ 4) (4 * (D / E x ^ 5)) x := by
  convert! (hd.inv hE).pow 4 using 1
  norm_num only [Pi.inv_apply, Nat.cast_ofNat, Nat.reduceSub, neg_neg]
  field_simp [hE]

theorem energy_inverse_fourth_lower_bound (E D : ℝ → ℝ) (c : ℝ)
    (hEc : ContinuousOn E (Ici 0)) (hEp : ∀ s, 0 ≤ s → 0 < E s)
    (hEd : ∀ s, 0 < s → HasDerivAt E (-D s) s)
    (hcoerc : ∀ s, 0 < s → c * E s ^ 5 ≤ D s)
    (t : ℝ) (ht : 0 ≤ t) :
    (E 0)⁻¹ ^ 4 + 4 * c * t ≤ (E t)⁻¹ ^ 4 := by
  let J : ℝ → ℝ := fun s => (E s)⁻¹ ^ 4 - 4 * c * s
  have hc : ContinuousOn (fun s => (E s)⁻¹ ^ 4) (Ici 0) :=
    (hEc.inv₀ (fun s hs => ne_of_gt (hEp s hs))).pow 4
  have hJc : ContinuousOn J (Icc 0 t) :=
    (hc.sub (continuousOn_const.mul continuousOn_id)).mono (fun _ hs => hs.1)
  have hJd (s : ℝ) (hs : s ∈ Ioo 0 t) :
      HasDerivAt J (4 * (D s / E s ^ 5) - 4 * c) s := by
    convert! (inverse_fourth_hasDerivAt (ne_of_gt (hEp s hs.1.le))
      (hEd s hs.1)).sub ((hasDerivAt_id s).const_mul (4 * c)) using 1
    simp
  have hmono : MonotoneOn J (Icc 0 t) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t) hJc
      (f' := fun s => 4 * (D s / E s ^ 5) - 4 * c)
    · intro s hs
      exact (hJd s (by simpa only [interior_Icc] using hs)).hasDerivWithinAt
    · intro s hs
      have hs' : s ∈ Ioo 0 t := by simpa only [interior_Icc] using hs
      have hdiv : c ≤ D s / E s ^ 5 :=
        (le_div_iff₀ (pow_pos (hEp s hs'.1.le) 5)).mpr (hcoerc s hs'.1)
      linarith
  have h := hmono (show 0 ∈ Icc 0 t from ⟨le_rfl, ht⟩)
    (show t ∈ Icc 0 t from ⟨ht, le_rfl⟩) ht
  dsimp only [J] at h
  linarith

theorem energy_le_fourthRoot_inverse (E D : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hEc : ContinuousOn E (Ici 0)) (hEp : ∀ s, 0 ≤ s → 0 < E s)
    (hEd : ∀ s, 0 < s → HasDerivAt E (-D s) s)
    (hcoerc : ∀ s, 0 < s → c * E s ^ 5 ≤ D s)
    (t : ℝ) (ht : 0 ≤ t) :
    E t ≤ 1 / fourthRoot ((E 0)⁻¹ ^ 4 + 4 * c * t) := by
  have hE0 := hEp 0 (by rfl)
  have hz : 0 < (E 0)⁻¹ ^ 4 + 4 * c * t := by positivity
  have hq := fourthRoot_pos hz
  have hpow := energy_inverse_fourth_lower_bound E D c hEc hEp hEd hcoerc t ht
  have hr : fourthRoot ((E 0)⁻¹ ^ 4 + 4 * c * t) ≤ (E t)⁻¹ := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0)
      (inv_nonneg.mpr (hEp t ht).le)
    rwa [fourthRoot_pow_four hz.le]
  apply (le_div_iff₀ hq).mpr
  have hm := mul_le_mul_of_nonneg_left hr (hEp t ht).le
  simpa only [mul_inv_cancel₀ (ne_of_gt (hEp t ht))] using hm

/-- A flexible positive-shift envelope, including every smaller shift than
the one determined by the initial energy. -/
theorem energy_le_shifted_fourthRoot (E D : ℝ → ℝ) (c B τ : ℝ)
    (hB : 0 < B) (hτ : 0 < τ)
    (hEc : ContinuousOn E (Ici 0)) (hEp : ∀ s, 0 ≤ s → 0 < E s)
    (hEd : ∀ s, 0 < s → HasDerivAt E (-D s) s)
    (hcoerc : ∀ s, 0 < s → c * E s ^ 5 ≤ D s)
    (hinit : E 0 ^ 4 * τ ≤ B ^ 4) (hcoef : 1 ≤ 4 * c * B ^ 4)
    (t : ℝ) (ht : 0 ≤ t) : E t ≤ B / fourthRoot (t + τ) := by
  have hE0 := hEp 0 (by rfl)
  have hEt := hEp t ht
  have hi : τ ≤ B ^ 4 * (E 0)⁻¹ ^ 4 := by
    have h := (le_div_iff₀ (pow_pos hE0 4)).mpr
      (show τ * E 0 ^ 4 ≤ B ^ 4 by nlinarith [hinit])
    simpa only [div_eq_mul_inv, inv_pow] using h
  have hc := mul_le_mul_of_nonneg_right hcoef ht
  have he := mul_le_mul_of_nonneg_left
    (energy_inverse_fourth_lower_bound E D c hEc hEp hEd hcoerc t ht)
    (pow_nonneg hB.le 4)
  have hz : 0 < t + τ := by linarith
  have hr : fourthRoot (t + τ) ≤ B * (E t)⁻¹ := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0)
      (mul_nonneg hB.le (inv_nonneg.mpr hEt.le))
    rw [fourthRoot_pow_four hz.le, mul_pow]
    nlinarith
  apply (le_div_iff₀ (fourthRoot_pos hz)).mpr
  calc
    E t * fourthRoot (t + τ) ≤ E t * (B * (E t)⁻¹) :=
      mul_le_mul_of_nonneg_left hr hEt.le
    _ = B := by field_simp

end FreeElasticScalar

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`FreeElasticScalar).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext, `Classical.choice, `Quot.sound] : Array Name).contains axiomName do
          throwError "Energy decay audit failed: {name} depends on {axiomName}"
      count := count + 1
  logInfo m!"CONDITIONAL_ENERGY_DECAY_AUDIT {count}: standard three axioms only."
