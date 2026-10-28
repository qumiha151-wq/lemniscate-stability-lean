import Lemniscate.AdjointTrialPairing
import Lemniscate.GeometricMomentTails

/-! Complete weighted tails of the normalized rotation's sine coefficients.
Only already certified coefficient majorants and geometric moments are used. -/
namespace Lemniscate.CoarseArithmetic

noncomputable def rotationSineCoefficient (j : ℕ) : ℝ :=
  2*(j+1:ℕ)*evenCoefficient thetaParameter nome (j+1)/rotationCoefficientNorm

private theorem rotation_coefficient_weight_bound (j k : ℕ) :
    |rotationSineCoefficient j| * (2*(j+1:ℕ):ℝ)^k ≤
      (2*(H:ℝ)/rotationCoefficientNorm)*2^k *
        (((j+1:ℕ):ℝ)^(k+2)*(qb:ℝ)^(j+1)) := by
  have hn := rotation_coefficient_norm_bounds.1
  have hb : 0 ≤ evenCoefficient thetaParameter nome (j+1) ∧
      evenCoefficient thetaParameter nome (j+1) ≤
        (H:ℝ)*(((j+1:ℕ):ℝ)*(qb:ℝ)^(j+1)) := by
    simpa only [fourierCoefficient,if_neg (by omega : j+1 ≠ 0)] using
      theta_nome_coefficient_majorant (j+1) (by omega)
  have hc : 0 ≤ rotationSineCoefficient j := by
    unfold rotationSineCoefficient
    exact div_nonneg (mul_nonneg (by positivity) hb.1) hn.le
  rw [abs_of_nonneg hc]
  have hm := mul_le_mul_of_nonneg_left hb.2 (by positivity : 0 ≤ 2*((j+1:ℕ):ℝ))
  have hd := div_le_div_of_nonneg_right hm hn.le
  have hw := mul_le_mul_of_nonneg_right hd
    (pow_nonneg (by positivity : (0:ℝ) ≤ 2*((j+1:ℕ):ℝ)) k)
  refine hw.trans_eq ?_
  simp only [mul_pow,pow_add,pow_two]
  ring

theorem rotation_sine_coefficient_tail (k : Fin 5) (N : ℕ) :
    Summable (fun n : ℕ => |rotationSineCoefficient (n+N)| *
      (2*(n+N+1:ℕ):ℝ)^k.val) ∧
    (∑' n : ℕ, |rotationSineCoefficient (n+N)| * (2*(n+N+1:ℕ):ℝ)^k.val) ≤
      (2*(H:ℝ)/rotationCoefficientNorm)*2^k.val * (momentTail (k.val+2) qb (N+1):ℝ) := by
  have hs := (moment_tail_sound (k.val+2) (by omega) qb (by norm_num [qb]) (N+1)).mul_left
    ((2*(H:ℝ)/rotationCoefficientNorm)*2^k.val)
  have hb (n : ℕ) := rotation_coefficient_weight_bound (n+N) k.val
  simp only [Nat.add_assoc] at hb
  have hn (n : ℕ) : 0 ≤ |rotationSineCoefficient (n+N)| * (2*(n+N+1:ℕ):ℝ)^k.val := by
    positivity
  have hsum := Summable.of_nonneg_of_le hn hb hs.summable
  refine ⟨hsum, ?_⟩
  simpa only [hs.tsum_eq,Nat.add_assoc] using hsum.tsum_le_tsum hb hs.summable

end Lemniscate.CoarseArithmetic
