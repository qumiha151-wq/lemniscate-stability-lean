import Lemniscate.PeriodicWeakUniqueness

/-! First weak derivatives on the actual periodic L2 space. The sign in the
test identity is checked with Mathlib's conjugate-linear first argument. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_frequency_factor_conj (n : ℤ) :
    conj (circleFrequencyFactor T n) = -circleFrequencyFactor T n := by
  simp only [circleFrequencyFactor, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem circle_complex_multiplier_duality (f g u v : CircleL2 T) (m : ℤ → ℂ)
    (hfg : ∀ n, fourierCoeff g n = m n * fourierCoeff f n)
    (huv : ∀ n, fourierCoeff v n = conj (m n) * fourierCoeff u n) :
    inner ℂ g u = inner ℂ f v := by
  rw [← (fourierBasis (T := T)).repr.inner_map_map g u,
    ← (fourierBasis (T := T)).repr.inner_map_map f v,
    lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [RCLike.inner_apply', fourierBasis_repr, hfg n, huv n, map_mul]
  ring

/-- Integration by parts against every periodic C1 test function. -/
def HasWeakCircleDeriv (f g : CircleL2 T) : Prop :=
  ∀ (φ φ₁ : C(AddCircle T, ℂ)), HasCircleDeriv T φ φ₁ →
    inner ℂ g (circleContinuousL2 T φ) = -inner ℂ f (circleContinuousL2 T φ₁)

theorem weak_circle_deriv_of_fourier (f g : CircleL2 T)
    (hfg : ∀ n : ℤ, fourierCoeff g n = circleFrequencyFactor T n * fourierCoeff f n) :
    HasWeakCircleDeriv T f g := by
  intro φ φ₁ hφ
  have h := circle_complex_multiplier_duality T f g (circleContinuousL2 T φ)
    ((-1 : ℂ) • circleContinuousL2 T φ₁) (circleFrequencyFactor T) hfg (by
      intro n
      rw [circle_fourierCoeff_smul, circle_continuous_l2_fourier,
        circle_continuous_l2_fourier, fourierCoeff_classical_deriv T φ φ₁ hφ,
        circle_frequency_factor_conj]
      ring)
  simpa only [inner_smul_right, neg_one_mul] using h

theorem fourier_of_weak_circle_deriv (f g : CircleL2 T) (hfg : HasWeakCircleDeriv T f g)
    (n : ℤ) :
    fourierCoeff g n = circleFrequencyFactor T n * fourierCoeff f n := by
  have h := hfg (fourier n) (circleFrequencyFactor T n • fourier n)
    (hasCircleDeriv_fourier T n)
  rw [circle_continuous_l2_fourier_basis, circle_continuous_l2_smul,
    circle_continuous_l2_fourier_basis, inner_smul_right] at h
  have hc := congrArg conj h
  simp only [map_neg, map_mul, circle_frequency_factor_conj, inner_conj_symm,
    neg_mul, neg_neg] at hc
  simpa only [← HilbertBasis.repr_apply_apply, fourierBasis_repr] using hc

theorem weak_circle_deriv_iff_fourier (f g : CircleL2 T) :
    HasWeakCircleDeriv T f g ↔
      ∀ n : ℤ, fourierCoeff g n = circleFrequencyFactor T n * fourierCoeff f n :=
  ⟨fourier_of_weak_circle_deriv T f g, weak_circle_deriv_of_fourier T f g⟩

theorem weak_circle_deriv_unique (f g h : CircleL2 T)
    (hfg : HasWeakCircleDeriv T f g) (hfh : HasWeakCircleDeriv T f h) : g = h := by
  apply circle_fourier_ext T
  intro n
  rw [fourier_of_weak_circle_deriv T f g hfg, fourier_of_weak_circle_deriv T f h hfh]

theorem weak_circle_second_of_deriv_chain (f g h : CircleL2 T)
    (hfg : HasWeakCircleDeriv T f g) (hgh : HasWeakCircleDeriv T g h) :
    HasWeakCircleSecond T f h := by
  intro φ φ₁ φ₂ h₁ h₂
  rw [hgh φ φ₁ h₁, hfg φ₁ φ₂ h₂, neg_neg]

end Lemniscate
