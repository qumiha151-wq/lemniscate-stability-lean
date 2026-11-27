import LengthGrowth.ActualFlow.TrigonometricPerturbation

noncomputable section
open MeasureTheory
namespace LengthGrowth.Multicover.Trigonometric

def scaledCurvature (n : ℕ) (m a A : ℝ) : Fn :=
  ⟨fun s => trigWave n s + (m + a*Real.cos s)/A, by fun_prop⟩

def scaledForce (n : ℕ) (m a A : ℝ) : Fn :=
  ⟨fun s => (n/A)^2 * trigSecond n s - a*Real.cos s/A^3 +
    (scaledCurvature n m a A s)^3 / 2, by fun_prop⟩

private theorem cubic_error {x f e : ℝ} (hx : |x| ≤ 4) (hf : |f| ≤ 3) (he : |x-f| ≤ 3*e) :
    |x^3/2 - f^3/2| ≤ 72*e := by
  have q : |x^2+x*f+f^2| ≤ 48 := by
    calc
      _ ≤ (|x^2|+|x*f|)+|f^2| := (abs_add_le ..).trans (add_le_add (abs_add_le ..) le_rfl)
      _ = |x|^2+|x| * |f|+|f|^2 := by rw [abs_pow, abs_pow, abs_mul]
      _ ≤ 48 := by nlinarith only [pow_le_pow_left₀ (abs_nonneg _) hx 2,
        pow_le_pow_left₀ (abs_nonneg _) hf 2, mul_le_mul hx hf (abs_nonneg _) (by norm_num)]
  calc
    _ = |x-f| * |x^2+x*f+f^2| / 2 := by
      rw [←abs_mul, ←abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num), ←abs_div]
      congr 1
      ring
    _ ≤ (3*e)*48/2 := by
      exact div_le_div_of_nonneg_right (mul_le_mul he q (abs_nonneg _) ((abs_nonneg _).trans he)) (by norm_num)
    _ = _ := by ring

/-- Uniform actual curvature and force bounds at every choice of the slow amplitude. -/
theorem scaled_errors {n : ℕ} {m a A : ℝ} (ha : |a| ≤ 3)
    (large : 1000000*(1+|m|) ≤ A) (near : |(n : ℝ)-A| ≤ 1) :
    (1+|m|)/A ≤ 1/1000000 ∧
    (∀ s, |scaledCurvature n m a A s - trigWave n s| ≤ 3*((1+|m|)/A)) ∧
    (∀ s, |scaledForce n m a A s - trigForce n s| ≤ 84*((1+|m|)/A)) := by
  have A1 : 1 ≤ A := by linarith only [large, abs_nonneg m]
  have Ap : 0 < A := by linarith
  let e := (1+|m|)/A
  have tiny : e ≤ 1/1000000 := by
    apply (div_le_iff₀ Ap).mpr
    linarith only [large]
  have inv₁ : 1/A ≤ e := div_le_div_of_nonneg_right (by linarith only [abs_nonneg m]) Ap.le
  have inv₂ : 1/A ≤ 1 := (div_le_iff₀ Ap).mpr (by simpa using A1)
  have ac s : |a*Real.cos s| ≤ 3 := by
    rw [abs_mul]
    simpa using mul_le_mul ha (abs_le.mpr ⟨Real.neg_one_le_cos s,Real.cos_le_one s⟩)
      (abs_nonneg _) (by norm_num : 0 ≤ (3:ℝ))
  have werr s : |scaledCurvature n m a A s - trigWave n s| ≤ 3*e := by
    change |trigWave n s + (m+a*Real.cos s)/A - trigWave n s| ≤ _
    rw [add_sub_cancel_left, abs_div, abs_of_pos Ap]
    change _ ≤ 3*((1+|m|)/A)
    rw [←mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith only [abs_add_le m (a*Real.cos s), ac s, abs_nonneg m]) Ap.le
  have ratio : |(n : ℝ)/A - 1| ≤ 1/A := by
    rw [show (n : ℝ)/A-1 = ((n : ℝ)-A)/A by field_simp, abs_div, abs_of_pos Ap]
    exact div_le_div_of_nonneg_right near Ap.le
  have r0 : 0 ≤ (n : ℝ) / A := by positivity
  have r2 : (n : ℝ) / A ≤ 2 := by linarith only [(abs_le.mp ratio).2,inv₂]
  have rerr : |((n : ℝ)/A)^2-1| ≤ 3*e := by
    rw [show ((n : ℝ)/A)^2-1 = ((n : ℝ)/A-1)*((n : ℝ)/A+1) by ring, abs_mul,
      abs_of_nonneg (by linarith only [r0] : 0 ≤ (n : ℝ)/A+1)]
    have z := mul_le_mul (ratio.trans inv₁) (show (n : ℝ)/A+1 ≤ 3 by linarith)
      (show 0 ≤ (n : ℝ)/A+1 by linarith) ((abs_nonneg _).trans (ratio.trans inv₁))
    linarith only [z]
  refine ⟨tiny, werr, fun s => ?_⟩
  have wbound : |scaledCurvature n m a A s| ≤ 4 := by
    have t := abs_add_le (scaledCurvature n m a A s - trigWave n s) (trigWave n s)
    rw [sub_add_cancel] at t
    linarith only [t, werr s, trigWave_bound n s, tiny]
  have c := cubic_error wbound (trigWave_bound n s) (werr s)
  have d : |(((n : ℝ)/A)^2-1)*trigSecond n s| ≤ 9*e := by
    rw [abs_mul]
    have z := mul_le_mul rerr (trigSecond_bound n s) (abs_nonneg _) ((abs_nonneg _).trans rerr)
    linarith only [z]
  have slow : |a*Real.cos s/A^3| ≤ 3*e := by
    rw [abs_div, abs_of_pos (pow_pos Ap 3)]
    have a3 : A ≤ A^3 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr A1) (sq_nonneg A), mul_nonneg (sub_nonneg.mpr A1) Ap.le]
    calc
      _ ≤ 3/A := div_le_div₀ (by norm_num) (ac s) Ap a3
      _ = 3*(1/A) := by ring
      _ ≤ 3*e := by linarith only [inv₁]
  change |(n/A)^2 * trigSecond n s - a*Real.cos s/A^3 + (scaledCurvature n m a A s)^3/2 -
    (trigSecond n s + (1/2) * (trigWave n s)^3)| ≤ _
  rw [show (n/A)^2 * trigSecond n s - a*Real.cos s/A^3 + (scaledCurvature n m a A s)^3/2 -
      (trigSecond n s + (1/2) * (trigWave n s)^3) =
      ((((n : ℝ)/A)^2-1)*trigSecond n s - a*Real.cos s/A^3) +
      ((scaledCurvature n m a A s)^3/2-(trigWave n s)^3/2) by ring]
  have diff := abs_add_le ((((n : ℝ)/A)^2-1)*trigSecond n s) (-(a*Real.cos s/A^3))
  rw [←sub_eq_add_neg, abs_neg] at diff
  change _ ≤ 84*e
  exact (abs_add_le ..).trans (by linarith only [diff,d,slow,c])

theorem prescribed_scaled_rate {n : ℕ} (hn : 0 < n) {m a A : ℝ} (ha : |a| ≤ 3)
    (large : 1000000*(1+|m|) ≤ A) (near : |(n : ℝ)-A| ≤ 1) :
    0 < average ((scaledCurvature n m a A)^2) *
      average (scaledCurvature n m a A * scaledForce n m a A)/2 - average ((scaledForce n m a A)^2) := by
  obtain ⟨tiny, w, f⟩ := scaled_errors ha large near
  exact positive_perturbed_rate hn _ _ tiny w f

end LengthGrowth.Multicover.Trigonometric
#print axioms LengthGrowth.Multicover.Trigonometric.prescribed_scaled_rate

