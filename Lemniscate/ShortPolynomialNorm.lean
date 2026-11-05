import Lemniscate.ShortCirclePolynomial
import Lemniscate.ShortSobolevNorm

namespace Lemniscate
open Complex Matrix MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0<T)]

theorem circle_short_polynomial_fourier (I : Finset ℤ) (a : ℤ → ℂ) (k : ℤ) :
    fourierCoeff ((∑ n∈I,a n • circleFourierH4 T (2*n):circleH4Domain T):CircleL2 T) k=
      ∑ n∈I,a n*(if k=2*n then 1 else 0) := by
  rw [← fourierBasis_repr,HilbertBasis.repr_apply_apply]
  have hb := orthonormal_iff_ite.mp (fourierBasis (T:=T)).orthonormal
  simp only [Submodule.coe_sum,Submodule.coe_smul_of_tower,inner_sum,inner_smul_right,
    circleFourierH4,hb]

theorem circle_short_polynomial_fourier_at (I : Finset ℤ) (a : ℤ → ℂ) (n : ℤ) :
    fourierCoeff ((∑ m∈I,a m • circleFourierH4 T (2*m):circleH4Domain T):CircleL2 T) (2*n)=
      if n∈I then a n else 0 := by
  rw [circle_short_polynomial_fourier]
  simp only [show ∀ m : ℤ,(2*n=2*m)↔n=m by intro m;omega]
  simp

theorem circle_short_polynomial_fourier_outside (I : Finset ℤ) (a : ℤ → ℂ) (k : ℤ)
    (hk : k∉I.image (fun n => 2*n)) :
    fourierCoeff ((∑ n∈I,a n • circleFourierH4 T (2*n):circleH4Domain T):CircleL2 T) k=0 := by
  rw [circle_short_polynomial_fourier]
  apply Finset.sum_eq_zero
  intro n hn
  have hne : k≠2*n := by
    intro heq
    exact hk (Finset.mem_image.mpr ⟨n,hn,heq.symm⟩)
  simp only [if_neg hne,mul_zero]

theorem circle_short_polynomial_even (I : Finset ℤ) (a : ℤ → ℂ)
    (k : ℤ) (hk : Odd k) :
    fourierCoeff ((∑ n∈I,a n • circleFourierH4 T (2*n):circleH4Domain T):CircleL2 T) k=0 := by
  apply circle_short_polynomial_fourier_outside
  intro hi
  rcases Finset.mem_image.mp hi with ⟨n,_,heq⟩
  rcases hk with ⟨m,hm⟩
  omega

theorem circle_short_polynomial_v_norm (I : Finset ℤ) (a : ℤ → ℂ) :
    shortVNorm T (∑ n∈I,a n • circleFourierH4 T (2*n))^2=
      ∑ n∈I,max (1:ℝ) ((2*(n:ℝ))^4)*‖a n‖^2 := by
  rw [short_v_norm_sq_fourier]
  rw [tsum_eq_sum (s:=I.image (fun n => 2*n)) (fun k hk => by
    rw [circle_short_polynomial_fourier_outside T I a k hk,norm_zero]
    ring)]
  rw [Finset.sum_image (fun n _ m _ hnm => by omega)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [circle_short_polynomial_fourier_at,if_pos hn]
  norm_cast

end Lemniscate
