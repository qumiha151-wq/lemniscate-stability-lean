import Lemniscate.ShortAdjointTrial
import Lemniscate.ShortAdjointWeightedDuality
import Lemniscate.ShortSobolevNorm

/-! Weighted duality on the genuine sine subspace, including completeness
of the positive sine coordinates and the actual weak second derivative. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ENNReal ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def shortSineSequence (f : CircleL2 T) : SineSequenceSpace := by
  have hi : Function.Injective (fun j : ℕ => 2*((j+1:ℕ):ℤ)) := by
    intro a b h
    change 2*((a+1:ℕ):ℤ) = 2*((b+1:ℕ):ℤ) at h
    omega
  have hs := (circle_fourier_square_summable T f).comp_injective hi
  have hm : Memℓp (fun j : ℕ => fourierCoeff f (2*((j+1:ℕ):ℤ))) 2 := by
    apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Function.comp_def] using hs
  exact ⟨fun j => evenSineFactor⁻¹*fourierCoeff f (2*((j+1:ℕ):ℤ)),
    hm.const_mul evenSineFactor⁻¹⟩

theorem short_sine_sequence_apply (f : CircleL2 T) (j : ℕ) :
    shortSineSequence T f j = evenSineFactor⁻¹*fourierCoeff f (2*((j+1:ℕ):ℤ)) := rfl

theorem short_sine_reconstruction (f : CircleL2 T) (hf : InCircleEvenSineSector T f) :
    circleEvenSineSynthesis T (shortSineSequence T f) = f := by
  apply (circle_sine_fourier_ext T f _ _ hf.1
    (circle_even_sine_coeff_neg T _) hf.2 (circle_even_sine_coeff_odd T _)).symm
  intro j
  cases j with
  | zero =>
    have hz := hf.1 0
    simp only [neg_zero] at hz
    simp only [Nat.cast_zero,mul_zero,circle_even_sine_coeff_zero]
    linear_combination (1/2:ℂ)*hz
  | succ j =>
    rw [circle_even_sine_coeff_pos,short_sine_sequence_apply]
    rw [mul_right_comm,inv_mul_cancel₀ evenSineFactor_ne_zero,one_mul]

theorem short_sine_norm_sq (f : CircleL2 T) (hf : InCircleEvenSineSector T f) :
    ‖f‖^2 = ∑' j : ℕ, ‖shortSineSequence T f j‖^2 := by
  calc
    _ = ‖circleEvenSineSynthesis T (shortSineSequence T f)‖^2 := by
      rw [short_sine_reconstruction T f hf]
    _ = _ := circle_even_sine_norm_sq T _

theorem short_sine_inner (f g : CircleL2 T)
    (hf : InCircleEvenSineSector T f) (hg : InCircleEvenSineSector T g) :
    (∑' j : ℕ, inner ℂ (shortSineSequence T f j) (shortSineSequence T g j)) =
      inner ℂ f g := by
  rw [← lp.inner_eq_tsum]
  rw [← (circleEvenSineSynthesis T).inner_map_map,
    short_sine_reconstruction T f hf,short_sine_reconstruction T g hg]

theorem short_sine_sequence_square (f : CircleL2 T) (j : ℕ) :
    ‖shortSineSequence T f j‖^2 = 2*‖fourierCoeff f (2*((j+1:ℕ):ℤ))‖^2 := by
  have hn := congrArg norm evenSineFactor_normalization
  simp only [norm_mul,norm_conj,norm_one] at hn
  norm_num at hn
  have hn2 : ‖evenSineFactor‖^2 = (1/2:ℝ) := by nlinarith only [hn]
  rw [short_sine_sequence_apply,norm_mul,mul_pow,norm_inv,inv_pow,hn2]
  norm_num

theorem short_sine_second_sector (f : circleH4Domain T)
    (hf : InCircleEvenSineSector T (f:CircleL2 T)) :
    InCircleEvenSineSector T (circleH4Jet T f).second := by
  have hw := weak_circle_second_of_deriv_chain T _ _ _
    (circleH4Jet T f).hfirst (circleH4Jet T f).hsecond
  constructor
  · intro n
    rw [fourier_of_weak_circle_second T _ _ hw,
      fourier_of_weak_circle_second T _ _ hw,hf.1]
    simp only [Int.cast_neg,neg_sq,mul_neg]
  · intro n
    rw [fourier_of_weak_circle_second T _ _ hw,hf.2,mul_zero]

theorem short_sine_second_square (f : circleH4Domain T) (j : ℕ) :
    ‖shortSineSequence T (circleH4Jet T f).second j‖^2 =
      shortAngularFrequency T^4*(2*((j+1:ℕ):ℝ))^4*
        ‖shortSineSequence T (f:CircleL2 T) j‖^2 := by
  rw [short_sine_sequence_square,short_h4_second_fourier_sq,
    short_sine_sequence_square]
  push_cast
  ring

theorem short_sine_affine_weight (f : circleH4Domain T)
    (hf : InCircleEvenSineSector T (f:CircleL2 T)) (a b : ℝ) :
    Summable (fun j : ℕ => (a*(2*((j+1:ℕ):ℝ))^4+b)*
      ‖shortSineSequence T (f:CircleL2 T) j‖^2) ∧
    (∑' j : ℕ, (a*(2*((j+1:ℕ):ℝ))^4+b)*
      ‖shortSineSequence T (f:CircleL2 T) j‖^2) =
      a*(shortAngularFrequency T)⁻¹^4*‖(circleH4Jet T f).second‖^2+
        b*‖(f:CircleL2 T)‖^2 := by
  have hκ : shortAngularFrequency T ≠ 0 := (short_angular_frequency_pos T).ne'
  have hs0 : Summable (fun j : ℕ => ‖shortSineSequence T (f:CircleL2 T) j‖^2) := by
    have h := lp.memℓp (shortSineSequence T (f:CircleL2 T))
    simpa only [memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal),
      ENNReal.toReal_ofNat,Real.rpow_two] using h
  have hs2 : Summable (fun j : ℕ => ‖shortSineSequence T (circleH4Jet T f).second j‖^2) := by
    have h := lp.memℓp (shortSineSequence T (circleH4Jet T f).second)
    simpa only [memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal),
      ENNReal.toReal_ofNat,Real.rpow_two] using h
  have hs4 : Summable (fun j : ℕ => (2*((j+1:ℕ):ℝ))^4*
      ‖shortSineSequence T (f:CircleL2 T) j‖^2) := by
    apply (hs2.mul_left ((shortAngularFrequency T)⁻¹^4)).congr
    intro j
    rw [short_sine_second_square]
    field_simp [hκ]
  have hsum4 : (∑' j : ℕ, (2*((j+1:ℕ):ℝ))^4*
      ‖shortSineSequence T (f:CircleL2 T) j‖^2) =
      (shortAngularFrequency T)⁻¹^4*‖(circleH4Jet T f).second‖^2 := by
    rw [short_sine_norm_sq T _ (short_sine_second_sector T f hf),← tsum_mul_left]
    apply tsum_congr
    intro j
    rw [short_sine_second_square]
    field_simp [hκ]
  have hs := (hs4.mul_left a).add (hs0.mul_left b)
  have he (j : ℕ) : a*((2*((j+1:ℕ):ℝ))^4*
      ‖shortSineSequence T (f:CircleL2 T) j‖^2)+
      b*‖shortSineSequence T (f:CircleL2 T) j‖^2 =
      (a*(2*((j+1:ℕ):ℝ))^4+b)*‖shortSineSequence T (f:CircleL2 T) j‖^2 := by ring
  refine ⟨hs.congr he, ?_⟩
  rw [← tsum_congr he, (hs4.mul_left a).tsum_add (hs0.mul_left b),
    tsum_mul_left,tsum_mul_left,hsum4,← short_sine_norm_sq T _ hf]
  ring

theorem short_sine_residual_square (g : CircleL2 T) :
    (∑' j : ℕ, ‖shortSineSequence T g j‖^2 / (shortResidualWeight (j+1):ℝ)) =
      circleShortResidualSquare T g := by
  simp only [short_sine_sequence_square,mul_div_assoc,tsum_mul_left,
    circleShortResidualSquare]

theorem short_circle_weighted_adjoint_duality (f : circleH4Domain T) (g : CircleL2 T)
    (hf : InCircleEvenSineSector T (f:CircleL2 T)) (hg : InCircleEvenSineSector T g) :
    |(inner ℂ (f:CircleL2 T) g).re| ≤
      Real.sqrt ((13/100:ℝ)*(shortAngularFrequency T)⁻¹^4*
        ‖(circleH4Jet T f).second‖^2+(75/2:ℝ)*‖(f:CircleL2 T)‖^2) *
      Real.sqrt (circleShortResidualSquare T g) := by
  let weight : ℕ → ℝ := fun j => (shortResidualWeight (j+1):ℝ)
  have hw (j : ℕ) : 0 < weight j := short_residual_weight_pos _
  have heq (j : ℕ) : weight j = (13/100:ℝ)*(2*((j+1:ℕ):ℝ))^4+75/2 := by
    simp only [weight,shortResidualWeight,Rat.cast_add,Rat.cast_mul,Rat.cast_div,
      Rat.cast_pow,Rat.cast_ofNat,Rat.cast_natCast]
  have hx := short_sine_affine_weight T f hf (13/100) (75/2)
  have hx' : Summable (fun j => weight j*‖shortSineSequence T (f:CircleL2 T) j‖^2) := by
    simpa only [heq] using hx.1
  have hy0 : Summable (fun j => ‖shortSineSequence T g j‖^2) := by
    have h := lp.memℓp (shortSineSequence T g)
    simpa only [memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal),
      ENNReal.toReal_ofNat,Real.rpow_two] using h
  have hy : Summable (fun j => ‖shortSineSequence T g j‖^2/weight j) := by
    apply Summable.of_nonneg_of_le (fun j => div_nonneg (sq_nonneg _) (hw j).le) _ hy0
    intro j
    apply div_le_self (sq_nonneg _)
    rw [heq]
    nlinarith [sq_nonneg ((2*((j+1:ℕ):ℝ))^2)]
  have h := (short_adjoint_weighted_sequence_duality weight hw
    (shortSineSequence T (f:CircleL2 T)) (shortSineSequence T g) hx' hy).2
  rw [short_sine_inner T _ _ hf hg] at h
  have hxs : (∑' j, weight j*‖shortSineSequence T (f:CircleL2 T) j‖^2) =
      (13/100:ℝ)*(shortAngularFrequency T)⁻¹^4*‖(circleH4Jet T f).second‖^2+
        (75/2:ℝ)*‖(f:CircleL2 T)‖^2 := by simpa only [heq] using hx.2
  have hys : (∑' j, ‖shortSineSequence T g j‖^2/weight j) =
      circleShortResidualSquare T g := short_sine_residual_square T g
  rw [hxs,hys] at h
  exact h

end Lemniscate
