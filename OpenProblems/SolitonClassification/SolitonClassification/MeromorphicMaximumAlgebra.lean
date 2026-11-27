import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

noncomputable section
open Complex
namespace ClosedSimilarity.MeromorphicGrowth

private theorem norm_six (a b c d e f : ℂ) :
    ‖a+b+c+d+e+f‖≤‖a‖+‖b‖+‖c‖+‖d‖+‖e‖+‖f‖ := by
  apply (norm_add_le _ _).trans
  apply add_le_add_left
  apply (norm_add_le _ _).trans
  apply add_le_add_left
  apply (norm_add_le _ _).trans
  apply add_le_add_left
  apply (norm_add_le _ _).trans
  apply add_le_add_left
  exact norm_add_le _ _

theorem maximum_amplitude_bound {a b u v w j l : ℂ} {h : ℝ} (hp : 1≤h)
    (size : h^2=1+‖u‖) (vB : ‖v‖≤4*h^3) (wB : ‖w‖≤8*h^4)
    (jB : ‖j‖≤24*h^5) (lB : ‖l‖≤96*h^6)
    (eq : 2*(u*l-v*j)+(3*(u^2*v^2)+5*(u^3*w))+u^6-2*a*u^2-2*b*v=0) :
    ‖u‖ ≤ 64*(472+2*‖a‖+8*‖b‖) := by
  let C := 472+2*‖a‖+8*‖b‖
  have Cpos : 1 ≤ C := by dsimp [C];linarith only [norm_nonneg a,norm_nonneg b]
  by_cases small : ‖u‖<1
  · change ‖u‖≤64*C
    linarith
  have h0 : 0≤h := by linarith
  have ub : ‖u‖≤h^2 := by linarith only [size]
  have relation : u^6= -(2*u*l)+(2*v*j)+(-(3*u^2*v^2))+(-(5*u^3*w))+
      (2*a*u^2)+(2*b*v) := by linear_combination eq
  have tri := norm_six (-(2*u*l)) (2*v*j) (-(3*u^2*v^2)) (-(5*u^3*w)) (2*a*u^2) (2*b*v)
  rw [←relation,norm_pow] at tri
  simp only [norm_neg,norm_mul,norm_pow,Complex.norm_ofNat] at tri
  have big : ‖u‖^6≤2*h^2*(96*h^6)+2*(4*h^3)*(24*h^5)+
      3*(h^2)^2*(4*h^3)^2+5*(h^2)^3*(8*h^4)+2*‖a‖*(h^2)^2+2*‖b‖*(4*h^3) := by
    apply tri.trans
    gcongr
  have eight : h^8≤h^10 := pow_le_pow_right₀ hp (by decide)
  have four : h^4≤h^10 := pow_le_pow_right₀ hp (by decide)
  have three : h^3≤h^10 := pow_le_pow_right₀ hp (by decide)
  have concl : ‖u‖^6≤C*h^10 := by
    dsimp [C]
    have A:=mul_le_mul_of_nonneg_left four (norm_nonneg a)
    have B:=mul_le_mul_of_nonneg_left three (norm_nonneg b)
    linarith only [big,eight,A,B]
  have s2 : h^2≤2*‖u‖ := by linarith only [size,le_of_not_gt small]
  have s6 := pow_le_pow_left₀ (sq_nonneg h) s2 6
  have h10 : 0 < h^10 := pow_pos (by linarith : 0<h) _
  have cap : h^2≤64*C := by
    apply (le_of_mul_le_mul_right _ h10)
    calc h^2*h^10 = (h^2)^6 := by ring
         _ ≤ (2*‖u‖)^6 := s6
         _ = 64*‖u‖^6 := by ring
         _ ≤ 64*(C*h^10) := by gcongr
         _ = 64*C*h^10 := by ring
  exact ub.trans cap

end ClosedSimilarity.MeromorphicGrowth

