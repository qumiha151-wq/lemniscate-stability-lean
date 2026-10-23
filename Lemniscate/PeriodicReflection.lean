import Lemniscate.PeriodicH4Fourier

/-! Reflection on the actual periodic L2 space, constructed by reversing Fourier
indices. It is a linear isometry and preserves the weak H4 domain. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ENNReal ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_inner_fourier (f g : CircleL2 T) :
    inner ℂ f g = ∑' n : ℤ, conj (fourierCoeff f n)*fourierCoeff g n := by
  rw [← (fourierBasis (T := T)).repr.inner_map_map f g, lp.inner_eq_tsum]
  simp only [RCLike.inner_apply', fourierBasis_repr]

theorem circle_reflected_coefficients_mem_l2 (f : CircleL2 T) :
    Memℓp (fun n : ℤ => fourierCoeff f (-n)) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Function.comp_def] using
    (circle_fourier_square_summable T f).comp_injective
      (show Function.Injective (fun n : ℤ => -n) from neg_injective)

noncomputable def circleReflect (f : CircleL2 T) : CircleL2 T :=
  (fourierBasis (T := T)).repr.symm
    ⟨fun n => fourierCoeff f (-n), circle_reflected_coefficients_mem_l2 T f⟩

theorem circle_reflect_fourier (f : CircleL2 T) (n : ℤ) :
    fourierCoeff (circleReflect T f) n = fourierCoeff f (-n) := by
  rw [← fourierBasis_repr]
  change ((fourierBasis (T := T)).repr ((fourierBasis (T := T)).repr.symm _)) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem circle_reflect_add (f g : CircleL2 T) :
    circleReflect T (f+g) = circleReflect T f + circleReflect T g := by
  apply circle_fourier_ext T
  intro n
  simp only [circle_reflect_fourier, circle_fourierCoeff_add]

theorem circle_reflect_smul (c : ℂ) (f : CircleL2 T) :
    circleReflect T (c • f) = c • circleReflect T f := by
  apply circle_fourier_ext T
  intro n
  simp only [circle_reflect_fourier, circle_fourierCoeff_smul]

theorem circle_reflect_involutive (f : CircleL2 T) :
    circleReflect T (circleReflect T f) = f := by
  apply circle_fourier_ext T
  intro n
  simp only [circle_reflect_fourier, neg_neg]

theorem circle_reflect_inner (f g : CircleL2 T) :
    inner ℂ (circleReflect T f) (circleReflect T g) = inner ℂ f g := by
  simp only [circle_inner_fourier, circle_reflect_fourier]
  exact (Equiv.neg ℤ).tsum_eq (fun n => conj (fourierCoeff f n)*fourierCoeff g n)

theorem circle_reflect_norm (f : CircleL2 T) : ‖circleReflect T f‖ = ‖f‖ := by
  have h : ‖circleReflect T f‖^2 = ‖f‖^2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), circle_reflect_inner]
  nlinarith [norm_nonneg f, norm_nonneg (circleReflect T f)]

noncomputable def circleReflectIsometry : CircleL2 T →ₗᵢ[ℂ] CircleL2 T where
  toFun := circleReflect T
  map_add' := circle_reflect_add T
  map_smul' := circle_reflect_smul T
  norm_map' := circle_reflect_norm T

theorem circle_reflect_mem_h4 (f : circleH4Domain T) :
    InCircleH4 T (circleReflect T (f : CircleL2 T)) := by
  apply circle_h4_of_fourth_fourier T _ (circleReflect T (circleH4Jet T f).fourth)
  intro n
  rw [circle_reflect_fourier, circle_h4_fourth_fourier, circle_frequency_factor_neg,
    circle_reflect_fourier]
  ring

noncomputable def circleReflectH4 (f : circleH4Domain T) : circleH4Domain T :=
  ⟨circleReflect T (f : CircleL2 T), circle_reflect_mem_h4 T f⟩

theorem circle_reflect_h4_first (f : circleH4Domain T) :
    (circleH4Jet T (circleReflectH4 T f)).first =
      (-1:ℂ) • circleReflect T (circleH4Jet T f).first := by
  apply circle_fourier_ext T
  intro n
  rw [fourier_of_weak_circle_deriv T _ _ (circleH4Jet T (circleReflectH4 T f)).hfirst,
    circle_fourierCoeff_smul, circle_reflect_fourier,
    fourier_of_weak_circle_deriv T _ _ (circleH4Jet T f).hfirst, circle_frequency_factor_neg]
  change circleFrequencyFactor T n * fourierCoeff (circleReflect T (f : CircleL2 T)) n = _
  rw [circle_reflect_fourier]
  ring

theorem circle_reflect_h4_second (f : circleH4Domain T) :
    (circleH4Jet T (circleReflectH4 T f)).second =
      circleReflect T (circleH4Jet T f).second := by
  apply circle_fourier_ext T
  intro n
  rw [fourier_of_weak_circle_deriv T _ _ (circleH4Jet T (circleReflectH4 T f)).hsecond,
    circle_reflect_h4_first, circle_fourierCoeff_smul, circle_reflect_fourier,
    circle_reflect_fourier, fourier_of_weak_circle_deriv T _ _ (circleH4Jet T f).hsecond,
    circle_frequency_factor_neg]
  ring

theorem circle_reflect_h4_fourth (f : circleH4Domain T) :
    (circleH4Jet T (circleReflectH4 T f)).fourth =
      circleReflect T (circleH4Jet T f).fourth := by
  apply circle_fourier_ext T
  intro n
  rw [circle_h4_fourth_fourier, circle_reflect_fourier, circle_h4_fourth_fourier,
    circle_frequency_factor_neg]
  change (circleFrequencyFactor T n)^4 * fourierCoeff (circleReflect T (f : CircleL2 T)) n = _
  rw [circle_reflect_fourier]
  ring

end Lemniscate
