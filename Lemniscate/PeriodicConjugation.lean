import Lemniscate.PeriodicReflectionSplit

/-! Complex conjugation on the actual L2 space, with its pointwise meaning,
Fourier formula, pairing identity, and compatibility with real coefficients. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleConjugate (f : CircleL2 T) : CircleL2 T := star f

theorem circle_conjugate_ae (f : CircleL2 T) :
    (circleConjugate T f : AddCircle T → ℂ) =ᵐ[AddCircle.haarAddCircle]
      fun x => conj (f x) := Lp.coeFn_star f

theorem circle_conjugate_fourier (f : CircleL2 T) (n : ℤ) :
    fourierCoeff (circleConjugate T f) n = conj (fourierCoeff f (-n)) := by
  simp only [fourierCoeff, neg_neg, smul_eq_mul]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [circle_conjugate_ae T f] with x hx
  rw [hx, map_mul, fourier_neg]

theorem circle_conjugate_add (f g : CircleL2 T) :
    circleConjugate T (f+g) = circleConjugate T f+circleConjugate T g := by
  apply circle_fourier_ext T
  intro n
  simp only [circle_conjugate_fourier, circle_fourierCoeff_add, map_add]

theorem circle_conjugate_sub (f g : CircleL2 T) :
    circleConjugate T (f-g) = circleConjugate T f-circleConjugate T g := by
  apply circle_fourier_ext T
  intro n
  simp only [circle_conjugate_fourier, circle_fourierCoeff_sub, map_sub]

theorem circle_conjugate_smul (c : ℂ) (f : CircleL2 T) :
    circleConjugate T (c • f) = conj c • circleConjugate T f := by
  apply circle_fourier_ext T
  intro n
  simp only [circle_conjugate_fourier, circle_fourierCoeff_smul, map_mul]

theorem circle_conjugate_involutive (f : CircleL2 T) :
    circleConjugate T (circleConjugate T f) = f := star_star f

theorem circle_conjugate_inner (f g : CircleL2 T) :
    inner ℂ (circleConjugate T f) (circleConjugate T g) = conj (inner ℂ f g) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [circle_conjugate_ae T f, circle_conjugate_ae T g] with x hf hg
  simp only [RCLike.inner_apply', hf, hg, map_mul, map_star]

theorem circle_conjugate_continuous_real (h : C(AddCircle T, ℂ))
    (hreal : ∀ x, conj (h x) = h x) :
    circleConjugate T (circleContinuousL2 T h) = circleContinuousL2 T h := by
  apply Lp.ext
  filter_upwards [circle_conjugate_ae T (circleContinuousL2 T h),
    ContinuousMap.coeFn_toLp (p := 2) AddCircle.haarAddCircle (𝕜 := ℂ) h] with x hc hh
  change circleConjugate T (circleContinuousL2 T h) x = circleContinuousL2 T h x
  change (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ h) x = h x at hh
  change circleContinuousL2 T h x = h x at hh
  rw [hc, hh, hreal]

theorem circle_conjugate_multiply (h : C(AddCircle T, ℂ))
    (hreal : ∀ x, conj (h x) = h x) (f : CircleL2 T) :
    circleConjugate T (circleMultiplyL2 T h f) =
      circleMultiplyL2 T h (circleConjugate T f) := by
  apply Lp.ext
  filter_upwards [circle_conjugate_ae T (circleMultiplyL2 T h f),
    circle_multiply_l2_ae T h f, circle_conjugate_ae T f,
    circle_multiply_l2_ae T h (circleConjugate T f)] with x hc hm hf hmc
  rw [hc, hm, hmc, hf, map_mul, hreal]

theorem circle_frequency_factor_conjugate_neg (n : ℤ) :
    conj (circleFrequencyFactor T (-n)) = circleFrequencyFactor T n := by
  rw [circle_frequency_factor_neg]
  simp [circleFrequencyFactor, map_mul, map_ofNat]

theorem circle_conjugate_weak_deriv (f g : CircleL2 T) (hg : HasWeakCircleDeriv T f g) :
    HasWeakCircleDeriv T (circleConjugate T f) (circleConjugate T g) := by
  apply weak_circle_deriv_of_fourier
  intro n
  rw [circle_conjugate_fourier, fourier_of_weak_circle_deriv T f g hg,
    map_mul, circle_frequency_factor_conjugate_neg, circle_conjugate_fourier]

end Lemniscate
