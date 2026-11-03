import Lemniscate.WeierstrassProfile
import Lemniscate.QuadraticODEUnique
import Lemniscate.PeriodicClassicalFourier

/-! Identification of a curvature square with the shifted Weierstrass
solution by the ODE and initial data. Only the scalar normalization remains
an input; no Fourier identity or solution-uniqueness hypothesis is assumed. -/
namespace Lemniscate
open Complex

theorem circle_profile_square_weierstrass (T : ℝ) (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1) (hq0 : q 0 = 1) (hp0 : p 0 = 0)
    (a : ℝ) (hnorm : 2*(a:ℂ)^2*unitSquarePeriods.weierstrassP (1/2) = 1) :
    (fun x : ℝ => (q (x:AddCircle T))^2) = normalizedWeierstrass a ∧
    (fun x : ℝ => 2*(q (x:AddCircle T)*p (x:AddCircle T))) =
      normalizedWeierstrassDerivative a := by
  let f : ℝ → ℂ := fun x => (q (x:AddCircle T))^2
  let f₁ : ℝ → ℂ := fun x => 2*(q (x:AddCircle T)*p (x:AddCircle T))
  have hf (x : ℝ) : HasDerivAt f (f₁ x) x := by
    convert! (hq x).fun_pow 2 using 1
    dsimp only [f₁]
    ring
  have hf₁ (x : ℝ) : HasDerivAt f₁ (1-3*(f x)^2) x := by
    convert! ((hq x).mul (hp x)).const_mul (2:ℂ) using 1
    change 1-3*((q (x:AddCircle T))^2)^2 =
      2*(p (x:AddCircle T)*p (x:AddCircle T)+q (x:AddCircle T)*(-(q (x:AddCircle T))^3))
    linear_combination -(he (x:AddCircle T))
  obtain ⟨hW0,hD0,hzero,hW⟩ := normalized_weierstrass_data a hnorm
  have h0 : f 0 = normalizedWeierstrass a 0 := by
    rw [hW0]
    change (q 0)^2 = 1
    rw [hq0,one_pow]
  have h1 : f₁ 0 = normalizedWeierstrassDerivative a 0 := by
    rw [hD0]
    change 2*(q 0*p 0) = 0
    rw [hp0,mul_zero,mul_zero]
  exact quadratic_second_order_unique f f₁ (normalizedWeierstrass a)
    (normalizedWeierstrassDerivative a) hf hf₁ (fun x => (hW x).1)
    (fun x => (hW x).2) h0 h1

end Lemniscate
