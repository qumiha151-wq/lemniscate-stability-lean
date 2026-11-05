import Lemniscate.ShortAdjointPairing
import Lemniscate.ShortAdjointTailData
import Lemniscate.ShortAdjointSineDuality
import Lemniscate.ShortSineSobolevTail
import Lemniscate.PeriodicNeutralTransform

/-! The actual positive rotation vector is the full new sine sequence.
This identification is independent of the previous finite approximation. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ENNReal ComplexConjugate

noncomputable def shortRotationSineSequence : SineSequenceSpace := by
  have hs : Summable (fun n : ℕ => ‖(shortRotationCoefficient n:ℂ)‖) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,Nat.add_zero,pow_zero,mul_one] using
      (short_rotation_coefficient_tail ⟨0,by decide⟩ 0).1
  have h1 : Memℓp (fun n : ℕ => (shortRotationCoefficient n:ℂ)) 1 := by
    apply (memℓp_gen_iff (by norm_num : 0 < (1:ℝ≥0∞).toReal)).mpr
    simpa using hs
  exact ⟨fun n => (shortRotationCoefficient n:ℂ),h1.of_exponent_ge (by norm_num)⟩

theorem short_rotation_sine_sequence_apply (j : ℕ) :
    shortRotationSineSequence j = (shortRotationCoefficient j:ℂ) := rfl

variable (T : ℝ) [Fact (0 < T)]

theorem short_sine_coordinate_pairing (f : CircleL2 T)
    (hf : InCircleEvenSineSector T f) (j : ℕ) :
    inner ℂ (circleEvenSineMode T j) f = shortSineSequence T f j := by
  have hn : conj evenSineFactor*2*evenSineFactor = 1 := by
    linear_combination evenSineFactor_normalization
  have hfactor : conj evenSineFactor*2 = evenSineFactor⁻¹ := by
    calc
      _ = (conj evenSineFactor*2*evenSineFactor)*evenSineFactor⁻¹ := by
        rw [mul_assoc,mul_inv_cancel₀ evenSineFactor_ne_zero,mul_one]
      _ = _ := by rw [hn,one_mul]
  change inner ℂ (evenSineFactor •
    (fourierBasis (T := T) (2*((j+1:ℕ):ℤ))-
      fourierBasis (T := T) (-(2*((j+1:ℕ):ℤ))))) f = _
  rw [inner_smul_left,inner_sub_left]
  simp only [← HilbertBasis.repr_apply_apply,fourierBasis_repr,hf.1,
    short_sine_sequence_apply]
  rw [← hfactor]
  ring

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
include hq hp he hqreal hpreal hs hc ho hr

theorem short_positive_rotation_sine_series :
    -circleUnitRotation T q p = circleEvenSineSynthesis T shortRotationSineSequence := by
  have hu := circle_even_sine_sector_of_symmetries T (circleUnitRotation T q p)
    (circle_unit_rotation_reflect T q p hq hs)
    (circle_even_frequency_part_eq_self T _ (circle_unit_rotation_no_odd T q p hq ho))
  have hf : InCircleEvenSineSector T (-circleUnitRotation T q p) := by
    simpa only [neg_one_smul] using circle_even_sine_sector_smul T (-1) _ hu
  calc
    _ = circleEvenSineSynthesis T (shortSineSequence T (-circleUnitRotation T q p)) :=
      (short_sine_reconstruction T _ hf).symm
    _ = _ := by
      congr 1
      ext j
      rw [← short_sine_coordinate_pairing T _ hf]
      exact circle_short_positive_rotation_pairing T q p hq hp he hqreal hpreal hs hc hr j

theorem short_positive_rotation_norm : ‖-circleUnitRotation T q p‖ = 1 := by
  have hb : ‖circleContinuousL2 T (q*p)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (circle_profile_rotation_ne_zero T q p hq hs hc ho)
  rw [norm_neg,circleUnitRotation,norm_smul,norm_inv,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ hb]

theorem short_positive_rotation_truncation_error :
    let e := -circleUnitRotationH4 T q p hq hp
    let g := circleSineTrialH4 T 7 (fun i => (shortRotationCoefficient i.val:ℂ))
    ‖((e-g:circleH4Domain T):CircleL2 T)‖ < (1/45000000:ℝ) ∧
      shortH1Norm T (e-g) < (19/50000000:ℝ) ∧
      shortVNorm T (e-g) < (3/500000:ℝ) := by
  let e := -circleUnitRotationH4 T q p hq hp
  let g := circleSineTrialH4 T 7 (fun i => (shortRotationCoefficient i.val:ℂ))
  have hf : (e:CircleL2 T) = circleEvenSineSynthesis T shortRotationSineSequence :=
    short_positive_rotation_sine_series T q p hq hp he hqreal hpreal hs hc ho hr
  have hseq (k : Fin 3) (N : ℕ) : Summable (fun n : ℕ =>
      ‖shortRotationSineSequence (n+N)‖*(2*((n+N+1:ℕ):ℝ))^k.val) := by
    simpa only [short_rotation_sine_sequence_apply,Complex.norm_real,Real.norm_eq_abs] using
      (short_rotation_coefficient_tail k N).1
  have hk (k : Fin 3) : (∑' n : ℕ, ‖shortRotationSineSequence (n+7)‖*
      (2*((n+7+1:ℕ):ℝ))^k.val) ≤ (shortRotationTailBound k:ℝ) := by
    have h := (short_rotation_coefficient_tail k 7).2
    simpa only [short_rotation_sine_sequence_apply,Complex.norm_real,Real.norm_eq_abs,
      shortRotationTailBound,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,Nat.reduceAdd] using h
  have hv : Summable (fun n : ℕ => ‖shortRotationSineSequence n‖*(2*((n+1:ℕ):ℝ))^2) := by
    simpa only [Nat.add_zero] using! hseq ⟨2,by decide⟩ 0
  have htail := short_sine_sobolev_tail T e shortRotationSineSequence hf hv 7
  simp only [short_rotation_sine_sequence_apply] at htail
  have hL2 := circle_sine_truncation_l2_error T shortRotationSineSequence
    (by simpa only [Nat.add_zero,pow_zero,mul_one] using! hseq ⟨0,by decide⟩ 0) 7
  rw [← hf] at hL2
  simp only [short_rotation_sine_sequence_apply] at hL2
  have hk0 : (∑' n : ℕ, ‖shortRotationSineSequence (n+7)‖) ≤
      (shortRotationTailBound 0:ℝ) := by
        simpa only [pow_zero,mul_one] using! hk ⟨0,by decide⟩
  have hs0 : Summable (fun n : ℕ => ‖shortRotationSineSequence (n+7)‖) := by
    simpa only [pow_zero,mul_one] using! hseq ⟨0,by decide⟩ 7
  have hs1 : Summable (fun n : ℕ => ‖shortRotationSineSequence (n+7)‖*
      (2*((n+7+1:ℕ):ℝ))) := by simpa only [pow_one] using! hseq ⟨1,by decide⟩ 7
  have hsum : (∑' n : ℕ, ‖shortRotationSineSequence (n+7)‖*
      (1+(2*((n+7+1:ℕ):ℝ)))) =
      (∑' n : ℕ, ‖shortRotationSineSequence (n+7)‖)+
        ∑' n : ℕ, ‖shortRotationSineSequence (n+7)‖*(2*((n+7+1:ℕ):ℝ)) := by
    rw [← hs0.tsum_add hs1]
    apply tsum_congr
    intro n
    ring
  have hL0 : ‖((e-g:circleH4Domain T):CircleL2 T)‖ ≤ (shortRotationTailBound 0:ℝ) := by
    apply hL2.trans
    simpa only [short_rotation_sine_sequence_apply] using hk0
  have hH1 : shortH1Norm T (e-g) ≤
      (shortRotationTailBound 0:ℝ)+(shortRotationTailBound ⟨1,by decide⟩:ℝ) := by
    apply htail.2.trans
    have h := add_le_add hk0 (by simpa only [pow_one] using! hk ⟨1,by decide⟩)
    rw [← hsum] at h
    simpa only [short_rotation_sine_sequence_apply] using h
  have hV : shortVNorm T (e-g) ≤ (shortRotationTailBound ⟨2,by decide⟩:ℝ) := htail.1.trans
    (by simpa only [short_rotation_sine_sequence_apply] using! hk ⟨2,by decide⟩)
  have hc0 := (Rat.cast_lt (K := ℝ)).mpr short_rotation_tail_comparisons.2.2.1
  have hc1 := (Rat.cast_lt (K := ℝ)).mpr short_rotation_tail_comparisons.2.2.2.1
  have hc2 := (Rat.cast_lt (K := ℝ)).mpr short_rotation_tail_comparisons.2.2.2.2
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_add] at hc0 hc1 hc2
  exact ⟨hL0.trans_lt hc0,hH1.trans_lt hc1,hV.trans_lt hc2⟩

end Profile

theorem short_rotation_sequence_second_summable :
    Summable (fun n : ℕ => ‖shortRotationSineSequence n‖*(2*((n+1:ℕ):ℝ))^2) := by
  simpa only [short_rotation_sine_sequence_apply,Complex.norm_real,Real.norm_eq_abs,
    Nat.add_zero] using! (short_rotation_coefficient_tail ⟨2,by decide⟩ 0).1

end Lemniscate

