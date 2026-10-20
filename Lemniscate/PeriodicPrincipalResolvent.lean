import Lemniscate.PeriodicBoundedMultiplier
import Lemniscate.PeriodicH4Fourier

/-! The resolvent of the fourth-order principal part at every positive real
parameter. It is a bounded operator on L2, has range in the actual H4 domain,
and is a two-sided inverse of lambda + 4 D^4 on that domain. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ENNReal

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circlePrincipalSymbol (r : ℝ) (n : ℤ) : ℂ :=
  ((r+4*(2*Real.pi/T)^4*(n:ℝ)^4 : ℝ) : ℂ)⁻¹

omit [Fact (0 < T)] in
theorem circle_principal_denominator_pos (r : ℝ) (hr : 0 < r) (n : ℤ) :
    0 < r+4*(2*Real.pi/T)^4*(n:ℝ)^4 := by positivity

omit [Fact (0 < T)] in
theorem circle_principal_symbol_bound (r : ℝ) (hr : 0 < r) (n : ℤ) :
    ‖circlePrincipalSymbol T r n‖ ≤ r⁻¹ := by
  rw [circlePrincipalSymbol, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (circle_principal_denominator_pos T r hr n)]
  apply (inv_le_inv₀ (circle_principal_denominator_pos T r hr n) hr).mpr
  exact le_add_of_nonneg_right (by positivity)

theorem circle_principal_fourth_symbol_bound (r : ℝ) (hr : 0 < r) (n : ℤ) :
    ‖(circleFrequencyFactor T n)^4*circlePrincipalSymbol T r n‖ ≤ (1/4:ℝ) := by
  have hw : 0 ≤ (2*Real.pi/T)^4*(n:ℝ)^4 := by positivity
  have hd := circle_principal_denominator_pos T r hr n
  rw [circle_frequency_factor_fourth, circlePrincipalSymbol, norm_mul, norm_inv,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hw, abs_of_pos hd, ← div_eq_mul_inv]
  apply (div_le_iff₀ hd).mpr
  nlinarith

theorem circle_principal_symbol_inverse (r : ℝ) (hr : 0 < r) (n : ℤ) :
    ((r:ℂ)+4*(circleFrequencyFactor T n)^4)*circlePrincipalSymbol T r n = 1 := by
  have hd : ((r+4*(2*Real.pi/T)^4*(n:ℝ)^4:ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (circle_principal_denominator_pos T r hr n))
  unfold circlePrincipalSymbol
  convert mul_inv_cancel₀ hd using 1
  rw [circle_frequency_factor_fourth]
  push_cast
  ring

noncomputable def circlePrincipalResolvent (r : ℝ) (hr : 0 < r) :
    CircleL2 T →L[ℂ] CircleL2 T :=
  circleBoundedMultiplier T (circlePrincipalSymbol T r) r⁻¹ (by positivity)
    (circle_principal_symbol_bound T r hr)

theorem circle_principal_resolvent_fourier (r : ℝ) (hr : 0 < r)
    (f : CircleL2 T) (n : ℤ) :
    fourierCoeff (circlePrincipalResolvent T r hr f) n =
      circlePrincipalSymbol T r n*fourierCoeff f n :=
  circle_bounded_multiplier_fourier T _ _ _ _ f n

theorem circle_principal_resolvent_norm_le (r : ℝ) (hr : 0 < r) :
    ‖circlePrincipalResolvent T r hr‖ ≤ r⁻¹ :=
  circle_bounded_multiplier_norm_le T _ _ _ _

theorem circle_principal_resolvent_mem_h4 (r : ℝ) (hr : 0 < r) (f : CircleL2 T) :
    InCircleH4 T (circlePrincipalResolvent T r hr f) := by
  apply (circle_h4_iff_fourth_coefficients T _).mpr
  have hm := circle_multiplier_coefficients_mem_l2 T
    (fun n => (circleFrequencyFactor T n)^4*circlePrincipalSymbol T r n)
    (1/4) (circle_principal_fourth_symbol_bound T r hr) f
  simpa only [circle_principal_resolvent_fourier, mul_assoc] using hm

noncomputable def circlePrincipalResolventH4 (r : ℝ) (hr : 0 < r) (f : CircleL2 T) :
    circleH4Domain T :=
  ⟨circlePrincipalResolvent T r hr f, circle_principal_resolvent_mem_h4 T r hr f⟩

/-- The shifted principal operator lambda I - (-4 D^4), with its H4 domain. -/
noncomputable def circlePrincipalShift (r : ℝ) : circleH4Domain T →ₗ[ℂ] CircleL2 T :=
  (r:ℂ) • (circleH4Domain T).subtype + (4:ℂ) • circleH4Derivative T 3

theorem circle_principal_shift_fourier (r : ℝ) (f : circleH4Domain T) (n : ℤ) :
    fourierCoeff (circlePrincipalShift T r f) n =
      ((r:ℂ)+4*(circleFrequencyFactor T n)^4)*fourierCoeff (f : CircleL2 T) n := by
  change fourierCoeff ((r:ℂ) • (f : CircleL2 T)+(4:ℂ) • (circleH4Jet T f).fourth) n = _
  rw [circle_fourierCoeff_add, circle_fourierCoeff_smul, circle_fourierCoeff_smul,
    circle_h4_fourth_fourier]
  ring

theorem circle_principal_resolvent_right_inverse (r : ℝ) (hr : 0 < r) (f : CircleL2 T) :
    circlePrincipalShift T r (circlePrincipalResolventH4 T r hr f) = f := by
  apply circle_fourier_ext T
  intro n
  rw [circle_principal_shift_fourier]
  change ((r:ℂ)+4*(circleFrequencyFactor T n)^4)*
    fourierCoeff (circlePrincipalResolvent T r hr f) n = _
  rw [circle_principal_resolvent_fourier, ← mul_assoc,
    circle_principal_symbol_inverse T r hr n, one_mul]

theorem circle_principal_resolvent_left_inverse (r : ℝ) (hr : 0 < r) (f : circleH4Domain T) :
    circlePrincipalResolvent T r hr (circlePrincipalShift T r f) = (f : CircleL2 T) := by
  apply circle_fourier_ext T
  intro n
  rw [circle_principal_resolvent_fourier, circle_principal_shift_fourier,
    ← mul_assoc, mul_comm (circlePrincipalSymbol T r n),
    circle_principal_symbol_inverse T r hr n, one_mul]

theorem circle_principal_shift_bijective (r : ℝ) (hr : 0 < r) :
    Function.Bijective (circlePrincipalShift T r) := by
  constructor
  · intro f g hfg
    apply Subtype.ext
    rw [← circle_principal_resolvent_left_inverse T r hr f,
      ← circle_principal_resolvent_left_inverse T r hr g, hfg]
  · intro f
    exact ⟨circlePrincipalResolventH4 T r hr f,
      circle_principal_resolvent_right_inverse T r hr f⟩

end Lemniscate
