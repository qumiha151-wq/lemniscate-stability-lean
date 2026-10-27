import Lemniscate.PeriodicSineSector

/-! Parseval on the even-frequency sine subspace, with the normalization
needed both for the rotation mode and for the adjoint residual. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ENNReal ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_even_sine_parseval (f : CircleL2 T) (hf : InCircleEvenSineSector T f) :
    ‖f‖^2 = 2*∑' j : ℕ, ‖fourierCoeff f (2*((j+1:ℕ):ℤ))‖^2 := by
  have hi : Function.Injective (fun j : ℕ => 2*((j+1:ℕ):ℤ)) := by
    intro a b h
    change 2*((a+1:ℕ):ℤ) = 2*((b+1:ℕ):ℤ) at h
    omega
  have hs := (circle_fourier_square_summable T f).comp_injective hi
  have hm : Memℓp (fun j : ℕ => fourierCoeff f (2*((j+1:ℕ):ℤ))) 2 := by
    apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Function.comp_def] using hs
  let v : SineSequenceSpace :=
    ⟨fun j => evenSineFactor⁻¹*fourierCoeff f (2*((j+1:ℕ):ℤ)),
      hm.const_mul evenSineFactor⁻¹⟩
  have hz : fourierCoeff f 0 = 0 := by
    have h := hf.1 0
    simp only [neg_zero] at h
    linear_combination (1/2:ℂ)*h
  have he : f = circleEvenSineSynthesis T v := by
    apply circle_sine_fourier_ext T _ _ _ hf.1 (circle_even_sine_coeff_neg T v)
      hf.2 (circle_even_sine_coeff_odd T v)
    intro j
    cases j with
    | zero => simpa only [Nat.cast_zero,mul_zero,circle_even_sine_coeff_zero] using hz
    | succ j =>
      rw [circle_even_sine_coeff_pos]
      change fourierCoeff f (2*((j+1:ℕ):ℤ)) =
        (evenSineFactor⁻¹*fourierCoeff f (2*((j+1:ℕ):ℤ)))*evenSineFactor
      rw [mul_right_comm, inv_mul_cancel₀ evenSineFactor_ne_zero, one_mul]
  have hn := congrArg norm evenSineFactor_normalization
  simp only [norm_mul,norm_conj,norm_one] at hn
  have hn2 : ‖evenSineFactor‖^2 = (1/2:ℝ) := by
    norm_num at hn
    nlinarith only [hn]
  have hni : ‖evenSineFactor⁻¹‖^2 = 2 := by
    rw [norm_inv,inv_pow,hn2]
    norm_num
  calc
    ‖f‖^2 = ‖circleEvenSineSynthesis T v‖^2 := by rw [he]
    _ = ∑' j : ℕ, ‖v j‖^2 := circle_even_sine_norm_sq T v
    _ = 2*∑' j : ℕ, ‖fourierCoeff f (2*((j+1:ℕ):ℤ))‖^2 := by
      simp only [v,norm_mul,mul_pow,hni,tsum_mul_left]

end Lemniscate
