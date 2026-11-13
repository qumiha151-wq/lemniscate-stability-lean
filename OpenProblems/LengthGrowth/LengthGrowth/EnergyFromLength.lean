import LengthGrowth.WeightedLengthComparison

/-! Conditional scalar energy decay from a quarter-power length envelope.
Only a positive weak virial coefficient is needed. The final geometric
wrapper must discharge all scalar premises from the actual flow. No length
derivative, monotonicity, or continuity hypothesis is used. -/

noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

namespace FreeElasticScalar

theorem energy_inverse_lower_of_quarter_length (L E D : ℝ → ℝ) (c A : ℝ)
    (hc : 0 < c) (hA : 0 < A) (hEc : ContinuousOn E (Ici 0))
    (hLp : ∀ x, 0 ≤ x → 0 < L x) (hEp : ∀ x, 0 ≤ x → 0 < E x)
    (hEd : ∀ x, 0 < x → HasDerivAt E (-D x) x)
    (hcoerc : ∀ x, 0 < x → c * E x ^ 2 / L x ^ 3 ≤ D x)
    (hLbound : ∀ x, 0 ≤ x → L x ≤ A * fourthRoot (1 + x))
    (t : ℝ) (ht : 0 ≤ t) :
    (E 0)⁻¹ + (4 * c / A ^ 3) * (fourthRoot (1 + t) - 1) ≤ (E t)⁻¹ := by
  let G : ℝ → ℝ := fun x => (E x)⁻¹ - (4 * c / A ^ 3) * fourthRoot (1 + x)
  have hqc : Continuous (fun x : ℝ => fourthRoot (1 + x)) :=
    fourthRoot_continuous.comp (continuous_const.add continuous_id)
  have hGc : ContinuousOn G (Icc 0 t) :=
    ((hEc.inv₀ (fun x hx => ne_of_gt (hEp x hx))).sub
      (continuousOn_const.mul hqc.continuousOn)).mono (fun _ hx => hx.1)
  have hGd (x : ℝ) (hx : x ∈ Ioo 0 t) :
      HasDerivAt G (D x / E x ^ 2 - c / (A ^ 3 * fourthRoot (1 + x) ^ 3)) x := by
    have hpos : 0 < 1 + x := by linarith [hx.1]
    have hqd := (fourthRoot_hasDerivAt hpos).comp x ((hasDerivAt_id x).const_add 1)
    simp only [mul_one] at hqd
    convert! ((hEd x hx.1).inv (ne_of_gt (hEp x hx.1.le))).sub
      (hqd.const_mul (4 * c / A ^ 3)) using 1
    norm_num only [Pi.inv_apply, neg_neg]
    field_simp [ne_of_gt (hEp x hx.1.le), ne_of_gt hA,
      ne_of_gt (fourthRoot_pos hpos)]
  have hmono : MonotoneOn G (Icc 0 t) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t) hGc
      (f' := fun x => D x / E x ^ 2 - c / (A ^ 3 * fourthRoot (1 + x) ^ 3))
    · intro x hx
      exact (hGd x (by simpa only [interior_Icc] using hx)).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Ioo 0 t := by simpa only [interior_Icc] using hx
      have hdiv : c / L x ^ 3 ≤ D x / E x ^ 2 := by
        apply (le_div_iff₀ (pow_pos (hEp x hx'.1.le) 2)).mpr
        convert! hcoerc x hx'.1 using 1
        ring
      have hpow : L x ^ 3 ≤ A ^ 3 * fourthRoot (1 + x) ^ 3 := by
        simpa only [mul_pow] using
          pow_le_pow_left₀ (hLp x hx'.1.le).le (hLbound x hx'.1.le) 3
      have hcomp := div_le_div_of_nonneg_left hc.le (pow_pos (hLp x hx'.1.le) 3) hpow
      exact sub_nonneg.mpr (hcomp.trans hdiv)
  have h := hmono (show 0 ∈ Icc 0 t from ⟨le_rfl, ht⟩)
    (show t ∈ Icc 0 t from ⟨ht, le_rfl⟩) ht
  have hq1 : fourthRoot (1 : ℝ) = 1 := by simp [fourthRoot]
  dsimp only [G] at h
  simp only [add_zero, hq1, mul_one] at h
  linarith

/-- A deliberately simple, nonoptimal decay constant. -/
theorem energy_decay_of_quarter_length (L E D : ℝ → ℝ) (c A : ℝ)
    (hc : 0 < c) (hA : 0 < A) (hEc : ContinuousOn E (Ici 0))
    (hLp : ∀ x, 0 ≤ x → 0 < L x) (hEp : ∀ x, 0 ≤ x → 0 < E x)
    (hEd : ∀ x, 0 < x → HasDerivAt E (-D x) x)
    (hcoerc : ∀ x, 0 < x → c * E x ^ 2 / L x ^ 3 ≤ D x)
    (hLbound : ∀ x, 0 ≤ x → L x ≤ A * fourthRoot (1 + x))
    (t : ℝ) (ht : 0 ≤ t) :
    E t ≤ (E 0 + A ^ 3 / (4 * c)) / fourthRoot (1 + t) := by
  let B := E 0 + A ^ 3 / (4 * c)
  have hE0 := hEp 0 (by rfl)
  have hEt := hEp t ht
  have hpart : 0 < A ^ 3 / (4 * c) := by positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have h0 : 1 / B ≤ (E 0)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hE0
      (show E 0 ≤ B by dsimp [B]; linarith)
  have hid : 1 / (A ^ 3 / (4 * c)) = 4 * c / A ^ 3 := by
    field_simp [ne_of_gt hA, ne_of_gt hc]
  have hd : 1 / B ≤ 4 * c / A ^ 3 := by
    simpa only [hid] using one_div_le_one_div_of_le hpart
      (show A ^ 3 / (4 * c) ≤ B by dsimp [B]; linarith)
  have hq1 : 1 ≤ fourthRoot (1 + t) := by
    have h := fourthRoot_mono (show (1 : ℝ) ≤ 1 + t by linarith)
    simpa only [fourthRoot, Real.sqrt_one] using h
  have hq : 0 < fourthRoot (1 + t) := by linarith
  have hinv := energy_inverse_lower_of_quarter_length L E D c A hc hA hEc
    hLp hEp hEd hcoerc hLbound t ht
  have hqB : fourthRoot (1 + t) / B ≤ (E t)⁻¹ := by
    calc
      fourthRoot (1 + t) / B = 1 / B + (1 / B) * (fourthRoot (1 + t) - 1) := by ring
      _ ≤ (E 0)⁻¹ + (4 * c / A ^ 3) * (fourthRoot (1 + t) - 1) :=
        add_le_add h0 (mul_le_mul_of_nonneg_right hd (sub_nonneg.mpr hq1))
      _ ≤ (E t)⁻¹ := hinv
  change E t ≤ B / fourthRoot (1 + t)
  apply (le_div_iff₀ hq).mpr
  have hh := mul_le_mul_of_nonneg_left ((div_le_iff₀ hB).mp hqB) hEt.le
  calc
    E t * fourthRoot (1 + t) ≤ E t * ((E t)⁻¹ * B) := hh
    _ = B := by rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hEt), one_mul]

/-- The same assumed length envelope and the derived energy envelope give
an actual scalar product cap; no separate product bound is an input. -/
theorem energy_length_cap_of_quarter_length (L E D : ℝ → ℝ) (c A : ℝ)
    (hc : 0 < c) (hA : 0 < A) (hEc : ContinuousOn E (Ici 0))
    (hLp : ∀ x, 0 ≤ x → 0 < L x) (hEp : ∀ x, 0 ≤ x → 0 < E x)
    (hEd : ∀ x, 0 < x → HasDerivAt E (-D x) x)
    (hcoerc : ∀ x, 0 < x → c * E x ^ 2 / L x ^ 3 ≤ D x)
    (hLbound : ∀ x, 0 ≤ x → L x ≤ A * fourthRoot (1 + x))
    (t : ℝ) (ht : 0 ≤ t) :
    E t * L t ≤ A * (E 0 + A ^ 3 / (4 * c)) := by
  have hb := energy_decay_of_quarter_length L E D c A hc hA hEc hLp hEp
    hEd hcoerc hLbound t ht
  have hE0 := hEp 0 (by rfl)
  have hq : 0 < fourthRoot (1 + t) := fourthRoot_pos (by linarith)
  have hB : 0 ≤ (E 0 + A ^ 3 / (4 * c)) / fourthRoot (1 + t) := by positivity
  calc
    E t * L t ≤ ((E 0 + A ^ 3 / (4 * c)) / fourthRoot (1 + t)) *
        (A * fourthRoot (1 + t)) :=
      mul_le_mul hb (hLbound t ht) (hLp t ht).le hB
    _ = A * (E 0 + A ^ 3 / (4 * c)) := by
      field_simp [ne_of_gt hq]

end FreeElasticScalar

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`FreeElasticScalar).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext, `Classical.choice, `Quot.sound] : Array Name).contains axiomName do
          throwError "Energy-from-length audit failed: {name} depends on {axiomName}"
      count := count + 1
  logInfo m!"ENERGY_FROM_LENGTH_AUDIT {count}: standard three axioms only."
