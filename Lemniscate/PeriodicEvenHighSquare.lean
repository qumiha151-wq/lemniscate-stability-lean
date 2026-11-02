import Lemniscate.PeriodicHighFourierNorm

/-! The square of the high even-frequency homogeneous H^{-2} seminorm.
Scalar identities and Young's inequality suffice for the finite-rank bounds. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleEvenHighSquare (f : CircleL2 T) : ℝ :=
  ∑' n : ℤ, if Even n ∧ 32 ≤ |(n:ℝ)| then ‖fourierCoeff f n‖^2/(n:ℝ)^4 else 0

theorem circle_even_high_square_nonneg (f : CircleL2 T) : 0 ≤ circleEvenHighSquare T f := by
  apply tsum_nonneg
  intro n
  split_ifs <;> positivity

theorem circle_even_high_square_smul (c : ℂ) (f : CircleL2 T) :
    circleEvenHighSquare T (c • f) = ‖c‖^2*circleEvenHighSquare T f := by
  have he (n : ℤ) : (if Even n ∧ 32 ≤ |(n:ℝ)| then
      ‖fourierCoeff (c • f) n‖^2/(n:ℝ)^4 else 0) =
      ‖c‖^2*(if Even n ∧ 32 ≤ |(n:ℝ)| then ‖fourierCoeff f n‖^2/(n:ℝ)^4 else 0) := by
    split_ifs <;> simp only [circle_fourierCoeff_smul,norm_mul,mul_pow,mul_div_assoc,mul_zero]
  simp only [circleEvenHighSquare,he,tsum_mul_left]

theorem circle_even_high_square_neg (f : CircleL2 T) :
    circleEvenHighSquare T (-f) = circleEvenHighSquare T f := by
  simpa only [neg_one_smul,norm_neg,norm_one,one_pow,one_mul] using
    circle_even_high_square_smul T (-1:ℂ) f

theorem circle_even_high_square_scaled_bound (c : ℂ) (g : CircleL2 T) (b H : ℝ)
    (hc : ‖c‖ ≤ b) (hg : circleEvenHighSquare T g ≤ H) :
    circleEvenHighSquare T (c • g) ≤ b^2*H := by
  rw [circle_even_high_square_smul]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg c) hc 2) hg
    (circle_even_high_square_nonneg T g) (sq_nonneg b)

theorem circle_even_high_square_add (f g : CircleL2 T) (p : ℝ) (hp : 0 < p) :
    circleEvenHighSquare T (f+g) ≤
      (1+p)*circleEvenHighSquare T f+(1+p⁻¹)*circleEvenHighSquare T g := by
  classical
  exact circle_high_fourier_add_square_bound T f g {n | Even n ∧ 32 ≤ |(n:ℝ)|}
    (fun n hn => hn.2) p hp

theorem circle_even_high_square_four_terms (a b c d : CircleL2 T) :
    circleEvenHighSquare T (a+b+c+d) ≤
      4*(circleEvenHighSquare T a+circleEvenHighSquare T b+
        circleEvenHighSquare T c+circleEvenHighSquare T d) := by
  have h := circle_even_high_square_add T (a+b) (c+d) 1 (by norm_num)
  have hab := circle_even_high_square_add T a b 1 (by norm_num)
  have hcd := circle_even_high_square_add T c d 1 (by norm_num)
  simp only [inv_one] at h hab hcd
  rw [show a+b+c+d = (a+b)+(c+d) by abel]
  linarith only [h,hab,hcd]

end Lemniscate
