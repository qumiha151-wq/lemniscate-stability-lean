import Lemniscate.PeriodicPrincipalResolvent

/-! Bounded first and second derivatives of the principal resolvent at p^2,
with explicit bounds tending to zero as p grows. These are actual weak
derivatives of its H4-valued output. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

theorem circle_frequency_factor_norm_fourth (n : ℤ) :
    ‖circleFrequencyFactor T n‖^4 = (2*Real.pi/T)^4*(n:ℝ)^4 := by
  calc
    _ = (‖circleFrequencyFactor T n‖^2)^2 := by ring
    _ = _ := by rw [circle_frequency_factor_norm_sq]; ring

theorem circle_principal_second_symbol_bound (p : ℝ) (hp : 0 < p) (n : ℤ) :
    ‖(circleFrequencyFactor T n)^2*circlePrincipalSymbol T (p^2) n‖ ≤ 1/(4*p) := by
  have hd : 0 < p^2+4*(2*Real.pi/T)^4*(n:ℝ)^4 := by positivity
  rw [norm_mul, norm_pow, circlePrincipalSymbol, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hd, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ hd (by positivity : 0 < 4*p)).mpr
  have he := circle_frequency_factor_norm_fourth T n
  nlinarith [sq_nonneg (p-2*‖circleFrequencyFactor T n‖^2)]

theorem circle_principal_first_symbol_bound (p : ℝ) (hp : 1 ≤ p) (n : ℤ) :
    ‖circleFrequencyFactor T n*circlePrincipalSymbol T (p^2) n‖ ≤ 5/(4*p) := by
  have hp' : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h₀ := circle_principal_symbol_bound T (p^2) (sq_pos_of_pos hp') n
  rw [← one_div] at h₀
  have hscale : 1/p^2 ≤ 1/p := by
    apply one_div_le_one_div_of_le hp'
    nlinarith
  have h₂ := circle_principal_second_symbol_bound T p hp' n
  rw [norm_mul, norm_pow] at h₂
  rw [norm_mul]
  have hx : ‖circleFrequencyFactor T n‖ ≤ 1+‖circleFrequencyFactor T n‖^2 := by
    nlinarith [sq_nonneg (‖circleFrequencyFactor T n‖-1)]
  calc
    _ ≤ (1+‖circleFrequencyFactor T n‖^2)*‖circlePrincipalSymbol T (p^2) n‖ :=
      mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ ≤ 1/p+1/(4*p) := by nlinarith
    _ = 5/(4*p) := by field_simp; ring

noncomputable def circlePrincipalFirst (p : ℝ) (hp : 1 ≤ p) :
    CircleL2 T →L[ℂ] CircleL2 T :=
  circleBoundedMultiplier T
    (fun n => circleFrequencyFactor T n*circlePrincipalSymbol T (p^2) n)
    (5/(4*p)) (by positivity) (circle_principal_first_symbol_bound T p hp)

noncomputable def circlePrincipalSecond (p : ℝ) (hp : 1 ≤ p) :
    CircleL2 T →L[ℂ] CircleL2 T :=
  circleBoundedMultiplier T
    (fun n => (circleFrequencyFactor T n)^2*circlePrincipalSymbol T (p^2) n)
    (1/(4*p)) (by positivity)
    (circle_principal_second_symbol_bound T p (lt_of_lt_of_le zero_lt_one hp))

theorem circle_principal_first_fourier (p : ℝ) (hp : 1 ≤ p) (f : CircleL2 T) (n : ℤ) :
    fourierCoeff (circlePrincipalFirst T p hp f) n =
      (circleFrequencyFactor T n*circlePrincipalSymbol T (p^2) n)*fourierCoeff f n :=
  circle_bounded_multiplier_fourier T _ _ _ _ f n

theorem circle_principal_second_fourier (p : ℝ) (hp : 1 ≤ p) (f : CircleL2 T) (n : ℤ) :
    fourierCoeff (circlePrincipalSecond T p hp f) n =
      ((circleFrequencyFactor T n)^2*circlePrincipalSymbol T (p^2) n)*fourierCoeff f n :=
  circle_bounded_multiplier_fourier T _ _ _ _ f n

theorem circle_principal_first_norm_le (p : ℝ) (hp : 1 ≤ p) :
    ‖circlePrincipalFirst T p hp‖ ≤ 5/(4*p) :=
  circle_bounded_multiplier_norm_le T _ _ _ _

theorem circle_principal_second_norm_le (p : ℝ) (hp : 1 ≤ p) :
    ‖circlePrincipalSecond T p hp‖ ≤ 1/(4*p) :=
  circle_bounded_multiplier_norm_le T _ _ _ _

theorem circle_principal_first_eq_jet (p : ℝ) (hp : 1 ≤ p) (f : CircleL2 T) :
    circlePrincipalFirst T p hp f =
      (circleH4Jet T (circlePrincipalResolventH4 T (p^2) (by nlinarith) f)).first := by
  apply circle_fourier_ext T
  intro n
  rw [fourier_of_weak_circle_deriv T _ _
    (circleH4Jet T (circlePrincipalResolventH4 T (p^2) (by nlinarith) f)).hfirst]
  change fourierCoeff (circlePrincipalFirst T p hp f) n =
    circleFrequencyFactor T n*fourierCoeff (circlePrincipalResolvent T (p^2) _ f) n
  rw [circle_principal_first_fourier, circle_principal_resolvent_fourier]
  ring

theorem circle_principal_second_eq_jet (p : ℝ) (hp : 1 ≤ p) (f : CircleL2 T) :
    circlePrincipalSecond T p hp f =
      (circleH4Jet T (circlePrincipalResolventH4 T (p^2) (by nlinarith) f)).second := by
  apply circle_fourier_ext T
  intro n
  rw [fourier_of_weak_circle_deriv T _ _
    (circleH4Jet T (circlePrincipalResolventH4 T (p^2) (by nlinarith) f)).hsecond,
    fourier_of_weak_circle_deriv T _ _
    (circleH4Jet T (circlePrincipalResolventH4 T (p^2) (by nlinarith) f)).hfirst]
  change fourierCoeff (circlePrincipalSecond T p hp f) n =
    circleFrequencyFactor T n*(circleFrequencyFactor T n*
      fourierCoeff (circlePrincipalResolvent T (p^2) _ f) n)
  rw [circle_principal_second_fourier, circle_principal_resolvent_fourier]
  ring

end Lemniscate
