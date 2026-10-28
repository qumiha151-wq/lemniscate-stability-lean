import Lemniscate.PeriodicSineAdjointTrial
import Lemniscate.PeriodicBlochOddLimit

/-! Exact derivative norms of normalized sine modes, for the paper's
finite Fourier truncation estimates. Orthogonality handles all orders at once. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

theorem circle_sine_h4_derivative_norm (j : Fin 4) (n : ℕ) :
    ‖circleH4Derivative T j (circleSineH4 T n)‖ =
      (2*Real.pi/T*(2*(n+1:ℕ):ℝ))^(j.val+1) := by
  let m : ℤ := 2*((n+1:ℕ):ℤ)
  have hm : m ≠ -m := by dsimp only [m]; omega
  have ho : inner ℂ (fourierBasis (T := T) m) (fourierBasis (T := T) (-m)) = 0 := by
    simpa only [hm,if_false] using
      orthonormal_iff_ite.mp (fourierBasis (T := T)).orthonormal m (-m)
  have hf : ‖evenSineFactor‖^2*2 = 1 := by
    have h := congrArg norm evenSineFactor_normalization
    simpa only [norm_mul,norm_conj,norm_ofNat,norm_one,pow_two,mul_assoc] using h
  have ha : 0 ≤ 2*Real.pi/T*(2*(n+1:ℕ):ℝ) := by
    have hT : 0 < T := Fact.out
    positivity
  have hfreq : ‖circleFrequencyFactor T m‖ = 2*Real.pi/T*(2*(n+1:ℕ):ℝ) := by
    simp only [circleFrequencyFactor,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      Complex.norm_I,mul_one]
    have hmcast : (m:ℝ) = (2*(n+1:ℕ):ℝ) := by dsimp only [m]; push_cast; ring
    rw [hmcast,← abs_mul,abs_of_nonneg ha]
  apply (sq_eq_sq₀ (norm_nonneg _) (pow_nonneg ha _)).mp
  simp only [circleSineH4,map_smul,map_sub,circle_h4_derivative_basis,norm_smul,mul_pow]
  change ‖evenSineFactor‖^2 *
    ‖(circleFrequencyFactor T m)^(j.val+1) • fourierBasis (T := T) m-
      (circleFrequencyFactor T (-m))^(j.val+1) • fourierBasis (T := T) (-m)‖^2 = _
  rw [norm_sub_sq (𝕜 := ℂ)]
  simp only [inner_smul_left,inner_smul_right,ho,mul_zero,map_zero,
    mul_zero,sub_zero,norm_smul,norm_pow,
    (fourierBasis (T := T)).orthonormal.norm_eq_one,mul_one,
    circle_frequency_factor_neg,norm_neg,hfreq]
  have hscale := congrArg (fun x : ℝ => x *
    ((2*Real.pi/T*(2*(n+1:ℕ):ℝ))^(j.val+1))^2) hf
  simp only [mul_pow] at hscale ⊢
  nlinarith only [hscale]

end Lemniscate
