import Lemniscate.OddFiniteForm
import Lemniscate.SobolevEntryBounds

/-! Sobolev weights at the actual odd Fourier frequencies. A summable distance
kernel controls every entry uniformly for alpha in the closed half interval. -/
namespace Lemniscate.OddArithmetic
open CoarseArithmetic

noncomputable def oddFrequencyWeight (i : ℤ) : ℝ := 1+(2*(i:ℝ)+1)^2
noncomputable def oddSobolevKernel (l : ℕ) : ℝ :=
  if l = 0 then 256 else (60*(rhi:ℝ)*(H:ℝ))*(l:ℝ)*(qb:ℝ)^l

theorem odd_frequency_weight_one_le (i : ℤ) : 1 ≤ oddFrequencyWeight i := by
  unfold oddFrequencyWeight
  linarith [sq_nonneg (2*(i:ℝ)+1)]

theorem odd_sobolev_kernel_nonneg (l : ℕ) : 0 ≤ oddSobolevKernel l := by
  have hH : 0 ≤ (H:ℝ) := by norm_num [H, rhi, qb]
  have hr : 0 ≤ (rhi:ℝ) := by norm_num [rhi]
  have hq : 0 ≤ (qb:ℝ) := by norm_num [qb]
  unfold oddSobolevKernel
  split_ifs <;> positivity

theorem odd_shift_square_bound (x α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    (x+α)^2 ≤ 2*(1+x^2) := by
  nlinarith [sq_nonneg (x-α), mul_nonneg hα (by linarith : 0 ≤ 1/2-α)]

theorem odd_shift_absolute_bound (x α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    |x+α| ≤ 1+x^2 := by
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (x-1/2), sq_nonneg (x+1/2)]

theorem odd_polynomial_sobolev_bound (n m : ℤ) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    |oddEntryPolynomial n m α| ≤ 60*(1+(n:ℝ)^2)*(1+(m:ℝ)^2) := by
  have hx := odd_shift_absolute_bound (n:ℝ) α hα hα'
  have hy := odd_shift_absolute_bound (m:ℝ) α hα hα'
  have hxy : |((n:ℝ)+α)*((m:ℝ)+α)| ≤ (1+(n:ℝ)^2)*(1+(m:ℝ)^2) := by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) (by positivity)
  have hd : ((n:ℝ)-(m:ℝ))^2 ≤ 2*((1+(n:ℝ)^2)*(1+(m:ℝ)^2)) := by
    nlinarith [sq_nonneg ((n:ℝ)+(m:ℝ)), mul_nonneg (sq_nonneg (n:ℝ)) (sq_nonneg (m:ℝ))]
  have hp := abs_le.mp hxy
  unfold oddEntryPolynomial
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg ((n:ℝ)-(m:ℝ)),
    mul_nonneg (sq_nonneg (n:ℝ)) (sq_nonneg (m:ℝ))]

theorem odd_diagonal_sobolev_bound (i : ℤ) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    |oddIndexedMatrix α i i| ≤ 256*(oddFrequencyWeight i)^2 := by
  let x : ℝ := 2*(i:ℝ)+1
  let w : ℝ := 1+x^2
  have hw : 1 ≤ w := by dsimp only [w]; linarith [sq_nonneg x]
  have hw0 : 0 ≤ w := by linarith
  have hw2 : w ≤ w^2 := by nlinarith [mul_nonneg hw0 (by linarith : 0 ≤ w-1)]
  have hs : (x+α)^2 ≤ 2*w := odd_shift_square_bound x α hα hα'
  have hs4 : (x+α)^4 ≤ 4*w^2 := by
    have ht := pow_le_pow_left₀ (sq_nonneg (x+α)) hs 2
    nlinarith
  have hr0 : 0 ≤ thetaParameter :=
    (by norm_num [rlo] : (0:ℝ) ≤ (rlo:ℝ)).trans (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])).1
  have hr1 : thetaParameter ≤ 1 := (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])).2.trans (by norm_num [rhi])
  have hrsq : thetaParameter^2 ≤ 1 := by nlinarith
  have hr4 := mul_le_mul_of_nonneg_right hrsq (by positivity : 0 ≤ (x+α)^4)
  have hr4pos : 0 ≤ thetaParameter^2*(x+α)^4 := by positivity
  have h0 := abs_le.mp (theta_times_coefficient_absolute_bound 0)
  have hlo := mul_le_mul_of_nonneg_right h0.1 (sq_nonneg (x+α))
  have hhi := mul_le_mul_of_nonneg_right h0.2 (sq_nonneg (x+α))
  have he : oddIndexedMatrix α i i =
      -4*thetaParameter^2*(x+α)^4+45*thetaParameter*fourierCoefficient thetaParameter nome 0*(x+α)^2-42 := by
    simp [oddIndexedMatrix, oddMatrixEntry, x]
  rw [he]
  change |-4*thetaParameter^2*(x+α)^4+
    45*thetaParameter*fourierCoefficient thetaParameter nome 0*(x+α)^2-42| ≤ 256*w^2
  apply abs_le.mpr
  constructor <;> nlinarith

theorem odd_indexed_half_distance (i j : ℤ) :
    ((2*i+1)-(2*j+1)).natAbs/2 = (i-j).natAbs := by
  rw [show (2*i+1)-(2*j+1) = 2*(i-j) by ring, Int.natAbs_mul]
  norm_num

theorem odd_off_sobolev_bound (i j : ℤ) (hne : i ≠ j) (α : ℝ)
    (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    |oddIndexedMatrix α i j| ≤
      ((60*(rhi:ℝ)*(H:ℝ))*((i-j).natAbs:ℝ)*(qb:ℝ)^((i-j).natAbs))*
        oddFrequencyWeight i*oddFrequencyWeight j := by
  have hfreq : 2*i+1 ≠ 2*j+1 := by omega
  have hb := odd_polynomial_sobolev_bound (2*i+1) (2*j+1) α hα hα'
  have hB : |oddEntryPolynomial (2*i+1) (2*j+1) α| ≤
      45*((4/3)*oddFrequencyWeight i*oddFrequencyWeight j) := by
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat] at hb
    convert! hb using 1 <;> unfold oddFrequencyWeight <;> ring
  have ht := odd_matrix_off_from_polynomial_bound (2*i+1) (2*j+1) ⟨i, rfl⟩ ⟨j, rfl⟩ hfreq α _ hB
  rw [odd_indexed_half_distance] at ht
  refine ht.trans_eq ?_
  ring

theorem odd_sobolev_entry_bound (i j : ℤ) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    |oddIndexedMatrix α i j| ≤
      oddSobolevKernel (i-j).natAbs*oddFrequencyWeight i*oddFrequencyWeight j := by
  by_cases he : i = j
  · subst j
    simpa only [sub_self, Int.natAbs_zero, oddSobolevKernel, ite_true, pow_two, mul_assoc] using
      odd_diagonal_sobolev_bound i α hα hα'
  · have hz : (i-j).natAbs ≠ 0 := by
      intro h
      have hh := Int.natAbs_eq_zero.mp h
      omega
    rw [oddSobolevKernel, if_neg hz]
    exact odd_off_sobolev_bound i j he α hα hα'

end Lemniscate.OddArithmetic
