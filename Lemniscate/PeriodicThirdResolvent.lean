import Lemniscate.PeriodicResolventSmoothing

/-! A coarse third-derivative resolvent bound at p^4. It supplies the only
additional derivative needed for the Bloch perturbation of the existing
fourth-order resolvent; no new domain or shifted Fourier basis is used. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T : ℝ) [Fact (0 < T)]

theorem circle_principal_third_symbol_bound (p : ℝ) (hp : 0 < p) (n : ℤ) :
    ‖(circleFrequencyFactor T n)^3*circlePrincipalSymbol T (p^4) n‖ ≤ 2/p := by
  have hd : 0 < p^4+4*(2*Real.pi/T)^4*(n:ℝ)^4 := by positivity
  rw [norm_mul,norm_pow,circlePrincipalSymbol,norm_inv,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hd,← div_eq_mul_inv]
  apply (div_le_div_iff₀ hd hp).mpr
  have he := circle_frequency_factor_norm_fourth T n
  by_cases hx : ‖circleFrequencyFactor T n‖ ≤ p
  · have hcube := pow_le_pow_left₀ (norm_nonneg (circleFrequencyFactor T n)) hx 3
    have hm := mul_le_mul_of_nonneg_right hcube hp.le
    have hn : 0 ≤ (2*Real.pi/T)^4*(n:ℝ)^4 := by positivity
    nlinarith only [hm,hn,pow_nonneg hp.le 4]
  · have hx' : p ≤ ‖circleFrequencyFactor T n‖ := (lt_of_not_ge hx).le
    have hm := mul_le_mul_of_nonneg_right hx' (pow_nonneg (norm_nonneg (circleFrequencyFactor T n)) 3)
    nlinarith only [hm,he,pow_nonneg hp.le 4,pow_nonneg (norm_nonneg (circleFrequencyFactor T n)) 4]

noncomputable def circlePrincipalThird (p : ℝ) (hp : 0 < p) : CircleL2 T →L[ℂ] CircleL2 T :=
  circleBoundedMultiplier T
    (fun n => (circleFrequencyFactor T n)^3*circlePrincipalSymbol T (p^4) n)
    (2/p) (by positivity) (circle_principal_third_symbol_bound T p hp)

theorem circle_principal_third_fourier (p : ℝ) (hp : 0 < p) (f : CircleL2 T) (n : ℤ) :
    fourierCoeff (circlePrincipalThird T p hp f) n =
      ((circleFrequencyFactor T n)^3*circlePrincipalSymbol T (p^4) n)*fourierCoeff f n :=
  circle_bounded_multiplier_fourier T _ _ _ _ f n

theorem circle_principal_third_norm_le (p : ℝ) (hp : 0 < p) :
    ‖circlePrincipalThird T p hp‖ ≤ 2/p :=
  circle_bounded_multiplier_norm_le T _ _ _ _

theorem circle_principal_third_eq_jet (p : ℝ) (hp : 0 < p) (f : CircleL2 T) :
    circlePrincipalThird T p hp f =
      (circleH4Jet T (circlePrincipalResolventH4 T (p^4) (by positivity) f)).third := by
  apply circle_fourier_ext T
  intro n
  rw [fourier_of_weak_circle_deriv T _ _
      (circleH4Jet T (circlePrincipalResolventH4 T (p^4) (by positivity) f)).hthird,
    fourier_of_weak_circle_deriv T _ _
      (circleH4Jet T (circlePrincipalResolventH4 T (p^4) (by positivity) f)).hsecond,
    fourier_of_weak_circle_deriv T _ _
      (circleH4Jet T (circlePrincipalResolventH4 T (p^4) (by positivity) f)).hfirst]
  change fourierCoeff (circlePrincipalThird T p hp f) n =
    circleFrequencyFactor T n*(circleFrequencyFactor T n*(circleFrequencyFactor T n*
      fourierCoeff (circlePrincipalResolvent T (p^4) (by positivity) f) n))
  rw [circle_principal_third_fourier,circle_principal_resolvent_fourier]
  ring

end Lemniscate
