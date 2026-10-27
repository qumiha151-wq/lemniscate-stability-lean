import Lemniscate.PeriodicRotationNorm
import Lemniscate.PeriodicSineParseval

/-! The exact mass of the rotation coefficients in the normalized sine basis.
This is the normalization identity used by the fixed rational adjoint trial. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_rotation_sine_mass (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (a : ℕ → ℝ)
    (hc : ∀ j : ℕ, 0 < j → fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (a j:ℂ)) :
    (∑' j : ℕ, (2*(j+1:ℕ)*a (j+1))^2) =
      2*(fourierCoeff (q^2 : C(AddCircle T, ℂ)) 0).re/(5*(2*Real.pi/T)^2) := by
  let f := circleContinuousL2 T ((2:ℂ) • (q*p))
  have hd (n : ℤ) : fourierCoeff f n =
      circleFrequencyFactor T n * fourierCoeff (q^2 : C(AddCircle T, ℂ)) n := by
    exact (circle_continuous_l2_fourier T _ n).trans
      (fourierCoeff_classical_deriv T _ _ (circle_profile_square_deriv T q p hq) n)
  have hf : InCircleEvenSineSector T f := by
    constructor
    · intro n
      rw [hd,hd,circle_frequency_factor_neg,hs,neg_mul]
    · intro n
      rw [hd,ho,mul_zero]
  have hcoeff (j : ℕ) : ‖fourierCoeff f (2*((j+1:ℕ):ℤ))‖^2 =
      (2*Real.pi/T)^2 * (2*(j+1:ℕ)*a (j+1))^2 := by
    rw [hd,hc (j+1) (by omega),norm_mul,mul_pow,circle_frequency_factor_norm_sq,
      Complex.norm_real,Real.norm_eq_abs,sq_abs]
    push_cast
    ring
  have hparseval := circle_even_sine_parseval T f hf
  simp only [hcoeff,tsum_mul_left] at hparseval
  have hnorm : ‖f‖^2 = 4*‖circleContinuousL2 T (q*p)‖^2 := by
    dsimp only [f]
    rw [circle_continuous_l2_smul,norm_smul,mul_pow]
    norm_num
  rw [hnorm,circle_rotation_norm_sq T q p hq hp he hqreal hpreal] at hparseval
  have hκ : 2*Real.pi/T ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (ne_of_gt (Fact.out : 0 < T))
  apply (eq_div_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 hκ))).mpr
  nlinarith only [hparseval]

end Lemniscate
