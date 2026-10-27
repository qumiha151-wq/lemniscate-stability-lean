import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! Exact identities from Sections 2--5 and Appendix A.
These statements do not assert the analytic or nonlinear stability theorem.
Every analytic hypothesis used in a scalar implication is explicit. -/
namespace Lemniscate

theorem linearization_zero_order (k ks kss : ℝ)
    (hss : kss = -2*k^3/9) (hs : ks^2 = 9-k^4/9) :
    3*ks^2+4*k*kss+(3/2:ℝ)*k^4+15/2 = 69/2+(5/18:ℝ)*k^4 := by
  rw [hss, hs]
  ring

theorem linearization_first_order (k ks : ℝ) :
    5*k*ks-(15/2:ℝ)*(k*ks/9) = (25/6:ℝ)*k*ks := by ring

theorem fourier_coefficient_identity (n m : ℝ) :
    45*m^2+(75/2:ℝ)*m*(n-m)-(15/2:ℝ)*(n-m)^2 =
      (15/2:ℝ)*n*(7*m-n) := by ring

theorem bloch_coefficient_expansion (n m a : ℝ) :
    (n+a)*(7*(m+a)-(n+a)) = n*(7*m-n)+(5*n+7*m)*a+6*a^2 := by ring

theorem symmetric_fourier_coefficient (n m : ℝ) :
    (15/4:ℝ)*(n*(7*m-n)+m*(7*n-m)) = 45*n*m-(15/4:ℝ)*(n-m)^2 := by ring

theorem formal_adjoint_constant (q : ℝ) :
    -(15/2:ℝ)*(1-3*q^4)-69/2-(45/2:ℝ)*q^4 = -42 := by ring

theorem weighted_young (x y t : ℝ) (ht : 0 < t) :
    2*x*y ≤ x^2/t+t*y^2 := by
  have he : x^2/t+t*y^2 = (x^2+t^2*y^2)/t := by field_simp
  rw [he]
  apply (le_div_iff₀ ht).mpr
  nlinarith [sq_nonneg (x-t*y)]

theorem garding_interpolation (energy xx mass : ℝ)
    (h : energy ≤ -4*xx^2+45*xx*mass-(153/4:ℝ)*mass^2) :
    energy ≤ -2*xx^2+(1719/8:ℝ)*mass^2 := by
  nlinarith [sq_nonneg (2*xx-(45/2:ℝ)*mass)]

theorem constrained_sine_dissipation (energy v2 f2 : ℝ)
    (hv : 0 ≤ v2) (he : energy ≤ (-100+2*63*(87/500:ℝ))*v2)
    (hf : f2 ≤ (1+(87/500:ℝ)^2)*v2) : energy ≤ -75*f2 := by
  nlinarith

theorem exact_center_cancellation (a h2 r : ℝ) (ha : a ≠ 0) :
    (a^2*h2-4*r^2*a^4)/a^2 = h2-4*r^2*a^2 := by
  field_simp

theorem exact_cross_cancellation (a h1 h2 h3 : ℝ) (ha : a ≠ 0) :
    (a*h1+a^2*h2+a^3*h3)/a = h1+a*h2+a^2*h3 := by
  field_simp

theorem comparison_error_budget :
    ((2660000:ℝ)+(1+7/4+7/8)*4200000)/10^11 = 17885/10^8 := by norm_num

theorem comparison_error_small : (17885:ℝ)/10^8 < 1/100 := by norm_num

theorem perturbation_margin (exactEnergy approximateEnergy mass : ℝ)
    (hm : 0 ≤ mass) (ha : approximateEnergy ≤ -(3/5:ℝ)*mass)
    (he : exactEnergy-approximateEnergy ≤ (1/100:ℝ)*mass) :
    exactEnergy ≤ -(1/2:ℝ)*mass := by linarith

theorem undo_bloch_congruence (a centerMass stableMass energy : ℝ)
    (ha : a^2 ≤ 1) (hs : 0 ≤ stableMass)
    (he : energy ≤ -(1/2:ℝ)*(a^2*centerMass+stableMass)) :
    energy ≤ -(a^2/2)*(centerMass+stableMass) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) hs]

theorem multiple_cover_gap (M a : ℝ) (hM : 0 < M) (ha : 1/M ≤ |a|) :
    1/(2*M^2) ≤ a^2/2 := by
  have hi : 0 ≤ 1/M := le_of_lt (one_div_pos.mpr hM)
  have hsq : (1/M)^2 ≤ |a|^2 := pow_le_pow_left₀ hi ha 2
  rw [sq_abs] at hsq
  have he : (1/M)^2/2 = 1/(2*M^2) := by field_simp
  rw [← he]
  linarith

theorem weighted_critical_exponents :
    (1/2:ℝ)*(3/4-1/4)+3/4-1/4 = 3/4 ∧
    (1:ℝ)*(3/4-1/4)+1/2-1/4 = 3/4 ∧
    (3/2:ℝ)*(3/4-1/4)+1/4-1/4 = 3/4 := by norm_num

end Lemniscate
