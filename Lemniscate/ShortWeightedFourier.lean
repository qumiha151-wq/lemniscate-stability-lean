import Lemniscate.ShortSobolevNorm
import Lemniscate.PeriodicBoundedMultiplier
import Lemniscate.ShortHouseholderNorm

/-! Actual weighted Fourier embeddings and their inverse-weight duals.
The duality identity allows Hilbert-space rank-one estimates to be applied to
the V and H1 seminorms, with the original L2 pairing unchanged. -/

noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate ENNReal

abbrev ShortFourierHilbert := lp (fun _ : ℤ => ℂ) 2

variable (T : ℝ) [Fact (0 < T)]

def shortWeightedFourier (w : ℤ → ℝ) (f : CircleL2 T)
    (hf : Summable (fun n : ℤ => w n ^ 2 * ‖fourierCoeff f n‖ ^ 2)) :
    ShortFourierHilbert :=
  ⟨fun n => (w n : ℂ) * fourierCoeff f n, by
    apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] using hf⟩

@[simp] theorem short_weighted_fourier_apply (w : ℤ → ℝ) (f : CircleL2 T)
    (hf : Summable (fun n : ℤ => w n ^ 2 * ‖fourierCoeff f n‖ ^ 2)) (n : ℤ) :
    shortWeightedFourier T w f hf n = (w n : ℂ) * fourierCoeff f n := rfl

theorem short_weighted_fourier_norm_sq (w : ℤ → ℝ) (f : CircleL2 T)
    (hf : Summable (fun n : ℤ => w n ^ 2 * ‖fourierCoeff f n‖ ^ 2)) :
    ‖shortWeightedFourier T w f hf‖ ^ 2 =
      ∑' n : ℤ, w n ^ 2 * ‖fourierCoeff f n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (shortWeightedFourier T w f hf)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, short_weighted_fourier_apply,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] using h

theorem short_inverse_weight_summable (w : ℤ → ℝ) (hw : ∀ n, 1 ≤ w n)
    (f : CircleL2 T) :
    Summable (fun n : ℤ => (w n)⁻¹ ^ 2 * ‖fourierCoeff f n‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _)) _
    (circle_fourier_square_summable T f)
  intro n
  have hpos : 0 < w n := lt_of_lt_of_le zero_lt_one (hw n)
  have hi : (w n)⁻¹ ≤ 1 := (inv_le_one₀ hpos).mpr (hw n)
  have hs := pow_le_pow_left₀ (inv_nonneg.mpr hpos.le) hi 2
  have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg ‖fourierCoeff f n‖)
  simpa only [one_pow, one_mul] using hm

def shortInverseWeightFourier (w : ℤ → ℝ) (hw : ∀ n, 1 ≤ w n) (f : CircleL2 T) :
    ShortFourierHilbert :=
  shortWeightedFourier T (fun n => (w n)⁻¹) f (short_inverse_weight_summable T w hw f)

@[simp] theorem short_inverse_weight_fourier_apply (w : ℤ → ℝ) (hw : ∀ n, 1 ≤ w n)
    (f : CircleL2 T) (n : ℤ) :
    shortInverseWeightFourier T w hw f n = (((w n)⁻¹ : ℝ) : ℂ) * fourierCoeff f n := rfl

/-- The inverse weighted vector represents the original L2 functional in the
weighted Hilbert coordinates; no weighted pairing identity is assumed. -/
theorem short_weighted_fourier_duality (w : ℤ → ℝ) (hw : ∀ n, 1 ≤ w n)
    (u f : CircleL2 T)
    (hf : Summable (fun n : ℤ => w n ^ 2 * ‖fourierCoeff f n‖ ^ 2)) :
    inner ℂ (shortInverseWeightFourier T w hw u) (shortWeightedFourier T w f hf) =
      inner ℂ u f := by
  rw [lp.inner_eq_tsum, ← (fourierBasis (T := T)).repr.inner_map_map u f,
    lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [RCLike.inner_apply', short_inverse_weight_fourier_apply,
    short_weighted_fourier_apply, fourierBasis_repr, map_mul, map_inv₀,
    Complex.conj_ofReal, Complex.ofReal_inv]
  have hn : (w n : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (lt_of_lt_of_le zero_lt_one (hw n))
  field_simp [hn]

def shortVWeight (n : ℤ) : ℝ := max 1 ((n : ℝ) ^ 2)

def shortH1Weight (n : ℤ) : ℝ := Real.sqrt (1 + (n : ℝ) ^ 2)

theorem short_v_weight_one_le (n : ℤ) : 1 ≤ shortVWeight n := le_max_left _ _

theorem short_h1_weight_one_le (n : ℤ) : 1 ≤ shortH1Weight n := by
  have h := Real.sqrt_le_sqrt
    (show (1 : ℝ) ≤ 1 + (n : ℝ) ^ 2 by nlinarith only [sq_nonneg (n : ℝ)])
  simpa only [Real.sqrt_one, shortH1Weight] using h

theorem short_v_weight_sq (n : ℤ) : shortVWeight n ^ 2 = max 1 ((n : ℝ) ^ 4) := by
  unfold shortVWeight
  by_cases hn : (1 : ℝ) ≤ (n : ℝ) ^ 2
  · have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hn 2
    have hfour : (1 : ℝ) ≤ (n : ℝ) ^ 4 := by nlinarith only [hh]
    rw [max_eq_right hn, max_eq_right hfour]
    ring
  · have hs : (n : ℝ) ^ 2 ≤ 1 := le_of_not_ge hn
    have hfour : (n : ℝ) ^ 4 ≤ 1 := by
      nlinarith only [hs, mul_nonneg (sq_nonneg (n : ℝ)) (sub_nonneg.mpr hs)]
    rw [max_eq_left hs, max_eq_left hfour]
    norm_num

theorem short_h1_weight_sq (n : ℤ) : shortH1Weight n ^ 2 = 1 + (n : ℝ) ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem short_v_weighted_coefficients_summable (f : circleH4Domain T) :
    Summable (fun n : ℤ => shortVWeight n ^ 2 *
      ‖fourierCoeff (f : CircleL2 T) n‖ ^ 2) := by
  simpa only [short_v_weight_sq] using short_v_weight_summable T f

theorem short_h1_weighted_coefficients_summable (f : circleH4Domain T) :
    Summable (fun n : ℤ => shortH1Weight n ^ 2 *
      ‖fourierCoeff (f : CircleL2 T) n‖ ^ 2) := by
  apply ((circle_fourier_square_summable T (f : CircleL2 T)).add
    (short_fourier_second_summable T f)).congr
  intro n
  rw [short_h1_weight_sq]
  ring

def shortVFourier : circleH4Domain T →ₗ[ℂ] ShortFourierHilbert where
  toFun f := shortWeightedFourier T shortVWeight (f : CircleL2 T)
    (short_v_weighted_coefficients_summable T f)
  map_add' f g := by
    apply lp.ext
    funext n
    change (shortVWeight n : ℂ) * fourierCoeff ((f : CircleL2 T) + (g : CircleL2 T)) n =
      (shortVWeight n : ℂ) * fourierCoeff (f : CircleL2 T) n +
        (shortVWeight n : ℂ) * fourierCoeff (g : CircleL2 T) n
    rw [circle_fourierCoeff_add, mul_add]
  map_smul' c f := by
    apply lp.ext
    funext n
    change (shortVWeight n : ℂ) * fourierCoeff (c • (f : CircleL2 T)) n = _
    rw [circle_fourierCoeff_smul]
    change (shortVWeight n : ℂ) * (c * fourierCoeff (f : CircleL2 T) n) =
      c * ((shortVWeight n : ℂ) * fourierCoeff (f : CircleL2 T) n)
    ring

def shortH1Fourier : circleH4Domain T →ₗ[ℂ] ShortFourierHilbert where
  toFun f := shortWeightedFourier T shortH1Weight (f : CircleL2 T)
    (short_h1_weighted_coefficients_summable T f)
  map_add' f g := by
    apply lp.ext
    funext n
    change (shortH1Weight n : ℂ) * fourierCoeff ((f : CircleL2 T) + (g : CircleL2 T)) n =
      (shortH1Weight n : ℂ) * fourierCoeff (f : CircleL2 T) n +
        (shortH1Weight n : ℂ) * fourierCoeff (g : CircleL2 T) n
    rw [circle_fourierCoeff_add, mul_add]
  map_smul' c f := by
    apply lp.ext
    funext n
    change (shortH1Weight n : ℂ) * fourierCoeff (c • (f : CircleL2 T)) n = _
    rw [circle_fourierCoeff_smul]
    change (shortH1Weight n : ℂ) * (c * fourierCoeff (f : CircleL2 T) n) =
      c * ((shortH1Weight n : ℂ) * fourierCoeff (f : CircleL2 T) n)
    ring

theorem short_v_fourier_norm (f : circleH4Domain T) : ‖shortVFourier T f‖ = shortVNorm T f := by
  apply (sq_eq_sq₀ (norm_nonneg _) (short_v_norm_nonneg T f)).mp
  change ‖shortWeightedFourier T shortVWeight (f : CircleL2 T)
    (short_v_weighted_coefficients_summable T f)‖ ^ 2 = _
  rw [short_weighted_fourier_norm_sq, short_v_norm_sq_fourier]
  simp only [short_v_weight_sq]

theorem short_h1_fourier_norm (f : circleH4Domain T) :
    ‖shortH1Fourier T f‖ = shortH1Norm T f := by
  apply (sq_eq_sq₀ (norm_nonneg _) (short_h1_norm_nonneg T f)).mp
  change ‖shortWeightedFourier T shortH1Weight (f : CircleL2 T)
    (short_h1_weighted_coefficients_summable T f)‖ ^ 2 = _
  rw [short_weighted_fourier_norm_sq, short_h1_norm_sq_fourier]
  simp only [short_h1_weight_sq]

theorem short_v_fourier_duality (u : CircleL2 T) (f : circleH4Domain T) :
    inner ℂ (shortInverseWeightFourier T shortVWeight short_v_weight_one_le u)
      (shortVFourier T f) = inner ℂ u (f : CircleL2 T) :=
  short_weighted_fourier_duality T shortVWeight short_v_weight_one_le u _
    (short_v_weighted_coefficients_summable T f)

theorem short_h1_fourier_duality (u : CircleL2 T) (f : circleH4Domain T) :
    inner ℂ (shortInverseWeightFourier T shortH1Weight short_h1_weight_one_le u)
      (shortH1Fourier T f) = inner ℂ u (f : CircleL2 T) :=
  short_weighted_fourier_duality T shortH1Weight short_h1_weight_one_le u _
    (short_h1_weighted_coefficients_summable T f)

theorem short_v_householder_norm (u : circleH4Domain T) (v : CircleL2 T)
    (s : ℝ) (hs : 1 < s) (hvu : inner ℂ v (u : CircleL2 T) = 2)
    (hproduct : s ^ 2 * shortVNorm T u ^ 2 *
      ‖shortInverseWeightFourier T shortVWeight short_v_weight_one_le v‖ ^ 2 ≤
        (s ^ 2 + 1) ^ 2) (f : circleH4Domain T) :
    shortVNorm T (f - inner ℂ v (f : CircleL2 T) • u) ≤ s * shortVNorm T f := by
  have h := short_rank_one_involution_norm (shortVFourier T u)
    (shortInverseWeightFourier T shortVWeight short_v_weight_one_le v) s hs
    (by rw [short_v_fourier_duality]; exact hvu)
    (by rw [short_v_fourier_norm]; exact hproduct) (shortVFourier T f)
  rw [short_v_fourier_duality] at h
  have he : shortVFourier T (f - inner ℂ v (f : CircleL2 T) • u) =
      shortVFourier T f - inner ℂ v (f : CircleL2 T) • shortVFourier T u := by
    rw [map_sub, map_smul]
  rw [← he, short_v_fourier_norm, short_v_fourier_norm] at h
  exact h

theorem short_h1_householder_norm (u : circleH4Domain T) (v : CircleL2 T)
    (s : ℝ) (hs : 1 < s) (hvu : inner ℂ v (u : CircleL2 T) = 2)
    (hproduct : s ^ 2 * shortH1Norm T u ^ 2 *
      ‖shortInverseWeightFourier T shortH1Weight short_h1_weight_one_le v‖ ^ 2 ≤
        (s ^ 2 + 1) ^ 2) (f : circleH4Domain T) :
    shortH1Norm T (f - inner ℂ v (f : CircleL2 T) • u) ≤ s * shortH1Norm T f := by
  have h := short_rank_one_involution_norm (shortH1Fourier T u)
    (shortInverseWeightFourier T shortH1Weight short_h1_weight_one_le v) s hs
    (by rw [short_h1_fourier_duality]; exact hvu)
    (by rw [short_h1_fourier_norm]; exact hproduct) (shortH1Fourier T f)
  rw [short_h1_fourier_duality] at h
  have he : shortH1Fourier T (f - inner ℂ v (f : CircleL2 T) • u) =
      shortH1Fourier T f - inner ℂ v (f : CircleL2 T) • shortH1Fourier T u := by
    rw [map_sub, map_smul]
  rw [← he, short_h1_fourier_norm, short_h1_fourier_norm] at h
  exact h

end Lemniscate
