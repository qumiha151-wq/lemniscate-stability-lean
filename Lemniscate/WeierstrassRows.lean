import Lemniscate.Algebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-! Integer rows of the square-lattice Weierstrass sum. -/
noncomputable section
namespace Lemniscate
open Complex
open scoped UpperHalfPlane

theorem integer_inverse_square_sum (z : ℂ) (hz : 0 < z.im) :
    (∑' n : ℤ, 1 / (z+n)^2) =
      -4*(Real.pi:ℂ)^2*Complex.exp (2*Real.pi*I*z) /
        (1-Complex.exp (2*Real.pi*I*z))^2 := by
  let E := Complex.exp (2*Real.pi*I*z)
  have hE : E ≠ 1 := by
    intro h
    have hnorm := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z,hz⟩
    change ‖E‖ < 1 at hnorm
    rw [h,norm_one] at hnorm
    exact (lt_irrefl _ hnorm)
  have hden : I*(1-E) ≠ 0 := mul_ne_zero I_ne_zero (sub_ne_zero.mpr hE.symm)
  have hlin : HasDerivAt (fun w : ℂ => 2*Real.pi*I*w) (2*Real.pi*I) z := by
    convert! (hasDerivAt_id z).const_mul (2*Real.pi*I) using 1
    simp only [mul_one]
  have hexp := (Complex.hasDerivAt_exp (2*Real.pi*I*z)).comp z hlin
  have hd := (((hexp.add_const 1).div ((hexp.const_sub 1).const_mul I) hden).const_mul
    (Real.pi:ℂ))
  have hvalue : (Real.pi:ℂ)*
      ((E*(2*Real.pi*I))*(I*(1-E))-(E+1)*(I*(-(E*(2*Real.pi*I))))) /
        (I*(1-E))^2 = 4*(Real.pi:ℂ)^2*E/(1-E)^2 := by
    field_simp
    ring_nf
  have hcot : HasDerivAt (fun w : ℂ => (Real.pi:ℂ)*cot (Real.pi*w))
      (4*(Real.pi:ℂ)^2*E/(1-E)^2) z := by
    rw [← hvalue]
    convert! hd using 1
    · ext w
      rw [Complex.cot_pi_eq_exp_ratio]
      rfl
    · dsimp only [E,Function.comp_def,Pi.div_apply]
      ring
  have hsum := iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow
    (k := 1) (z := z) (by norm_num) hz
  rw [iteratedDerivWithin_one,hcot.hasDerivWithinAt.derivWithin
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn z hz)] at hsum
  norm_num only [pow_one,Nat.factorial_one,mul_one,Nat.reduceAdd,neg_one_mul] at hsum
  change _ = -4*(Real.pi:ℂ)^2*E/(1-E)^2
  linear_combination hsum

theorem integer_half_shift_difference (y : ℝ) (hy : 0 < y) :
    (∑' n : ℤ, 1 / ((1/2:ℂ)+I*y+n)^2) -
      (∑' n : ℤ, 1 / (I*y+n)^2) =
    ((4*Real.pi^2*Real.exp (-2*Real.pi*y)/(1+Real.exp (-2*Real.pi*y))^2 +
      4*Real.pi^2*Real.exp (-2*Real.pi*y)/(1-Real.exp (-2*Real.pi*y))^2 : ℝ):ℂ) := by
  have hi : 0 < (I*(y:ℂ)).im := by simpa using hy
  have hh : 0 < ((1/2:ℂ)+I*y).im := by simpa using hy
  have h0 : Complex.exp (2*Real.pi*I*(I*y)) = (Real.exp (-2*Real.pi*y):ℂ) := by
    rw [show (2:ℂ)*Real.pi*I*(I*y) = ((-2*Real.pi*y:ℝ):ℂ) by
      push_cast; ring_nf; simp only [Complex.I_sq]; ring]
    exact (Complex.ofReal_exp _).symm
  have h1 : Complex.exp (2*Real.pi*I*((1/2:ℂ)+I*y)) =
      -(Real.exp (-2*Real.pi*y):ℂ) := by
    rw [show (2:ℂ)*Real.pi*I*((1/2:ℂ)+I*y) =
      Real.pi*I+((-2*Real.pi*y:ℝ):ℂ) by
        push_cast; ring_nf; simp only [Complex.I_sq]; ring]
    rw [Complex.exp_add,Complex.exp_pi_mul_I,← Complex.ofReal_exp,neg_one_mul]
  rw [integer_inverse_square_sum _ hh,integer_inverse_square_sum _ hi,h0,h1]
  push_cast
  simp only [sub_neg_eq_add,mul_neg]
  ring

end Lemniscate
