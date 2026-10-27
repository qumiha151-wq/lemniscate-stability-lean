import Lemniscate.PeriodicProfileBounds

/-! The exact L2 norm of the rotation mode follows from the profile ODE and
its first integral, without a special-function integration formula. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_real_square_mean (h : C(AddCircle T, ℂ))
    (hreal : ∀ x, conj (h x) = h x) :
    (fourierCoeff (h^2 : C(AddCircle T, ℂ)) 0).re = ‖circleContinuousL2 T h‖^2 := by
  have hconstant : circleContinuousL2 T (1 : C(AddCircle T, ℂ)) =
      fourierBasis (T := T) 0 := by
    rw [show (1 : C(AddCircle T, ℂ)) = fourier 0 by ext x; simp]
    exact circle_continuous_l2_fourier_basis T 0
  have hs := circle_real_square_pairing T h hreal
    (circleContinuousL2 T (1 : C(AddCircle T, ℂ)))
  rw [circle_multiply_l2_continuous, circle_multiply_l2_continuous,
    mul_one, mul_one, hconstant] at hs
  simpa only [← HilbertBasis.repr_apply_apply, fourierBasis_repr,
    circle_continuous_l2_fourier] using hs

theorem circle_rotation_square_mean (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1) :
    5 * fourierCoeff ((q*p)^2 : C(AddCircle T, ℂ)) 0 =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) 0 := by
  have hd : HasCircleDeriv T (q^3*p) ((3:ℂ) • (q*p)^2-q^6) := by
    intro x
    convert! ((hq x).pow 3).mul (hp x) using 1
    change 3*(q (x:AddCircle T)*p (x:AddCircle T))^2-(q (x:AddCircle T))^6 =
      (3*(q (x:AddCircle T))^2*p (x:AddCircle T))*p (x:AddCircle T)+
      (q (x:AddCircle T))^3*(-(q (x:AddCircle T))^3)
    ring
  have hz := fourierCoeff_classical_deriv T _ _ hd 0
  simp only [circle_continuous_fourier_sub, circle_continuous_fourier_smul,
    circleFrequencyFactor, Int.cast_zero, Complex.ofReal_zero, zero_mul, mul_zero] at hz
  have hi : (2:ℂ) • (q*p)^2+q^6 = q^2 := by
    ext x
    change 2*(q x*p x)^2+(q x)^6 = (q x)^2
    calc
      _ = (q x)^2*(2*(p x)^2+(q x)^4) := by ring
      _ = _ := by rw [he]; ring
  have hm := congrArg (fun f : C(AddCircle T, ℂ) => fourierCoeff f 0) hi
  rw [circle_continuous_fourier_add, circle_continuous_fourier_smul] at hm
  linear_combination hm + hz

theorem circle_rotation_norm_sq (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x) :
    ‖circleContinuousL2 T (q*p)‖^2 = (fourierCoeff (q^2 : C(AddCircle T, ℂ)) 0).re/5 := by
  have hm := congrArg Complex.re (circle_rotation_square_mean T q p hq hp he)
  have hs := circle_real_square_mean T (q*p) (by
    intro x
    change conj (q x*p x) = q x*p x
    rw [map_mul, hqreal, hpreal])
  norm_num [Complex.mul_re] at hm
  change 5*(fourierCoeff ((q*p)^2 : C(AddCircle T, ℂ)) 0).re =
    (fourierCoeff (q^2 : C(AddCircle T, ℂ)) 0).re at hm
  linarith

end Lemniscate
