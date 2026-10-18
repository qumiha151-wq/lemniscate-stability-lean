import Lemniscate.PeriodicFourierProducts

/-! The profile ODE and first integral imply (q^2)'' = 1 - 3*q^4.
We prove the resulting Fourier identity, including its exceptional zero mode.
Existence and identification of the particular Jacobi profile are not assumed proved. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

theorem circle_profile_square_deriv (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) :
    HasCircleDeriv T (q^2) ((2:ℂ) • (q*p)) := by
  intro x
  convert! (hq x).pow 2 using 1
  change 2*(q (x:AddCircle T)*p (x:AddCircle T)) = _
  ring

theorem circle_profile_square_second (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1) :
    HasCircleDeriv T ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) := by
  intro x
  have hid : 2*(p (x:AddCircle T))^2 - 2*(q (x:AddCircle T))^4 =
      1-3*(q (x:AddCircle T))^4 := by
    calc
      _ = (2*(p (x:AddCircle T))^2+(q (x:AddCircle T))^4) -
          3*(q (x:AddCircle T))^4 := by ring
      _ = _ := by rw [he]
  convert! ((hq x).mul (hp x)).const_mul (2:ℂ) using 1
  change 1-3*(q (x:AddCircle T))^4 =
    2*(p (x:AddCircle T)*p (x:AddCircle T) +
      q (x:AddCircle T)*(-(q (x:AddCircle T))^3))
  rw [← hid]
  ring

theorem circle_profile_fourth_fourier (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1) (n : ℤ) :
    3 * fourierCoeff (q^4 : C(AddCircle T, ℂ)) n = (if n = 0 then 1 else 0) +
      (((2*Real.pi/T)^2*(n:ℝ)^2:ℝ):ℂ) * fourierCoeff (q^2 : C(AddCircle T, ℂ)) n := by
  have hd := fourierCoeff_classical_second T (q^2) ((2:ℂ) • (q*p))
    (1-(3:ℂ) • (q^4)) (circle_profile_square_deriv T q p hq)
    (circle_profile_square_second T q p hq hp he) n
  rw [circle_continuous_fourier_sub, circle_continuous_fourier_one,
    circle_continuous_fourier_smul] at hd
  push_cast at hd ⊢
  linear_combination -hd

theorem circle_profile_fourth_mean (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1) :
    fourierCoeff (q^4 : C(AddCircle T, ℂ)) 0 = 1/3 := by
  have hd := circle_profile_fourth_fourier T q p hq hp he 0
  norm_num at hd ⊢
  linear_combination (1/3:ℂ) * hd

end Lemniscate
