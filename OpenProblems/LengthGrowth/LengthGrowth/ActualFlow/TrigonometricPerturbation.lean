import LengthGrowth.ActualFlow.TrigonometricOutwardWave

noncomputable section
open MeasureTheory
namespace LengthGrowth.Multicover.Trigonometric

def average : Fn →ₗ[ℝ] ℝ := period⁻¹ • mass period

theorem average_eq (g : Fn) : average g = (mass period g) / period := by
  simp [average, div_eq_inv_mul]

theorem average_one : average 1 = 1 := by
  rw [average_eq, mass_one, div_self period_pos.ne']

theorem average_mono {g h : Fn} (le : ∀ s, g s ≤ h s) : average g ≤ average h := by
  rw [average_eq, average_eq]
  exact div_le_div_of_nonneg_right (mass_mono _ period_pos.le _ _ (fun s _ => le s)) period_pos.le

theorem average_abs_le {g : Fn} {C : ℝ} (bound : ∀ s, |g s| ≤ C) : |average g| ≤ C := by
  have constant (r : ℝ) : average (r • (1 : Fn)) = r := by
    simp [average_one]
  apply abs_le.mpr
  constructor
  · rw [←constant (-C)]
    exact average_mono (fun s => by simpa [smul_eq_mul] using (abs_le.mp (bound s)).1)
  · rw [←constant C]
    exact average_mono (fun s => by simpa [smul_eq_mul] using (abs_le.mp (bound s)).2)

private theorem abs_offset {a b d : ℝ} (ha : |a-b| ≤ d) : |a| ≤ |b|+d := by
  calc
    |a| = |b+(a-b)| := by ring_nf
    _ ≤ |b|+|a-b| := abs_add_le .. 
    _ ≤ _ := by linarith only [ha]

private theorem product_error {x y f g X Y F G : ℝ} (hx : |x-f| ≤ X)
    (hy : |y-g| ≤ Y) (hf : |f| ≤ F) (hb : |y| ≤ G) :
    |x*y-f*g| ≤ X*G+F*Y := by
  calc
    _ = |(x-f)*y+f*(y-g)| := by ring_nf
    _ ≤ |(x-f)*y|+|f*(y-g)| := abs_add_le ..
    _ = |x-f| * |y| + |f| * |y-g| := by rw [abs_mul, abs_mul]
    _ ≤ _ := add_le_add (mul_le_mul hx hb (abs_nonneg _) ((abs_nonneg _).trans hx))
      (mul_le_mul hf hy (abs_nonneg _) ((abs_nonneg _).trans hf))

theorem trigWave_bound (n : ℕ) (s : ℝ) : |trigWave n s| ≤ 3 := by
  change |2*Real.cos _+Real.cos _/32| ≤ 3
  apply abs_le.mpr
  constructor <;> linarith only [Real.neg_one_le_cos ((n : ℝ)*s),
    Real.cos_le_one ((n : ℝ)*s), Real.neg_one_le_cos (3*((n : ℝ)*s)), Real.cos_le_one (3*((n : ℝ)*s))]

theorem trigSecond_bound (n : ℕ) (s : ℝ) : |trigSecond n s| ≤ 3 := by
  change |-2*Real.cos _-9*Real.cos _/32| ≤ 3
  apply abs_le.mpr
  constructor <;> linarith only [Real.neg_one_le_cos ((n : ℝ)*s),
    Real.cos_le_one ((n : ℝ)*s), Real.neg_one_le_cos (3*((n : ℝ)*s)), Real.cos_le_one (3*((n : ℝ)*s))]

theorem trigForce_bound (n : ℕ) (s : ℝ) : |trigForce n s| ≤ 17 := by
  change |trigSecond n s+1/2*(trigWave n s)^3| ≤ 17
  have pw := pow_le_pow_left₀ (abs_nonneg _) (trigWave_bound n s) 3
  calc
    _ ≤ |trigSecond n s|+|1/2*(trigWave n s)^3| := abs_add_le ..
    _ = |trigSecond n s|+1/2*|trigWave n s|^3 := by rw [abs_mul, abs_pow]; norm_num
    _ ≤ 17 := by linarith only [pw, trigSecond_bound n s]

private theorem averaged_moments {n : ℕ} (hn : 0 < n) :
    average ((trigWave n)^2) = 4097/2048 ∧
    average (trigWave n * trigForce n) = 17801219/16777216 ∧
    average ((trigForce n)^2) = 60523245573/68719476736 := by
  simp only [average_eq, wave_square hn, wave_force hn, force_square hn,
    mul_div_cancel_right₀ _ period_pos.ne', and_self]

/-- The outward sign persists under explicit uniform perturbations of curvature and force. -/
theorem positive_perturbed_rate {n : ℕ} (hn : 0 < n) (w h : Fn) {e : ℝ}
    (he : e ≤ 1/1000000)
    (ew : ∀ s, |w s - trigWave n s| ≤ 3*e)
    (eh : ∀ s, |h s - trigForce n s| ≤ 84*e) :
    0 < average (w^2) * average (w*h) / 2 - average (h^2) := by
  have wb s : |w s| ≤ 4 := by linarith only [abs_offset (ew s), trigWave_bound n s, he]
  have hb s : |h s| ≤ 18 := by linarith only [abs_offset (eh s), trigForce_bound n s, he]
  have bounds {a b : Fn} {C : ℝ} (h : ∀ s, |a s - b s| ≤ C) : |average a - average b| ≤ C := by
    rw [←map_sub]
    exact average_abs_le h
  obtain ⟨bb, jj, dd⟩ := averaged_moments hn
  have berror := bounds (a:=w^2) (b:=(trigWave n)^2) (C:=21*e) (fun s => by
    change |(w s)^2-(trigWave n s)^2| ≤ _
    simpa only [sq, show 3*e*4+3*(3*e)=21*e by ring] using
      product_error (ew s) (ew s) (trigWave_bound n s) (wb s))
  have jerror := bounds (a:=w*h) (b:=trigWave n * trigForce n) (C:=306*e) (fun s => by
    change |w s*h s-trigWave n s*trigForce n s| ≤ _
    simpa only [show 3*e*18+3*(84*e)=306*e by ring] using
      product_error (ew s) (eh s) (trigWave_bound n s) (hb s))
  have derror := bounds (a:=h^2) (b:=(trigForce n)^2) (C:=2940*e) (fun s => by
    change |(h s)^2-(trigForce n s)^2| ≤ _
    simpa only [sq, show 84*e*18+17*(84*e)=2940*e by ring] using
      product_error (eh s) (eh s) (trigForce_bound n s) (hb s))
  have jbound : |average (w*h)| ≤ 72 := average_abs_le (fun s => by
    change |w s*h s| ≤ 72
    rw [abs_mul]
    exact (mul_le_mul (wb s) (hb s) (abs_nonneg _) (by norm_num)).trans (by norm_num))
  have berr : |average ((trigWave n)^2)| ≤ 3 := by rw [bb]; norm_num
  have pr := product_error berror jerror berr jbound
  rw [bb,jj] at pr
  rw [dd] at derror
  linarith only [(abs_le.mp pr).1, (abs_le.mp derror).2, he]

end LengthGrowth.Multicover.Trigonometric
#print axioms LengthGrowth.Multicover.Trigonometric.positive_perturbed_rate

