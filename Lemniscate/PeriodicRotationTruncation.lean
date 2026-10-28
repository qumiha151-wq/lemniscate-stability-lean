import Lemniscate.RotationCoefficientTails
import Lemniscate.PeriodicSineTruncation
import Lemniscate.PeriodicTrialNormalization
import Lemniscate.PeriodicNeutralTransform
import Lemniscate.PeriodicTruncationRescale

/-! Identify the actual normalized rotation with its complete sine series,
then bound its H4 Fourier truncation error by certified geometric moments. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate ENNReal

noncomputable def rotationSineSequence : SineSequenceSpace := by
  refine ⟨fun n => (rotationSineCoefficient n:ℂ), ?_⟩
  have hs : Summable (fun n : ℕ => ‖(rotationSineCoefficient n:ℂ)‖) := by
    simpa only [Fin.val_zero,Nat.add_zero,pow_zero,mul_one,Complex.norm_real,Real.norm_eq_abs] using
      (rotation_sine_coefficient_tail ⟨0,by decide⟩ 0).1
  have h1 : Memℓp (fun n : ℕ => (rotationSineCoefficient n:ℂ)) 1 := by
    apply (memℓp_gen_iff (by norm_num : 0 < (1:ℝ≥0∞).toReal)).mpr
    simpa using hs
  exact h1.of_exponent_ge (by norm_num)

variable (T : ℝ) [Fact (0 < T)]

private theorem sine_reconstruction (f : CircleL2 T) (hf : InCircleEvenSineSector T f)
    (v : SineSequenceSpace) (hp : ∀ j : ℕ, inner ℂ (circleEvenSineMode T j) f = v j) :
    f = circleEvenSineSynthesis T v := by
  have hc (j : ℕ) : fourierCoeff f (2*((j+1:ℕ):ℤ)) = v j*evenSineFactor := by
    have h := hp j
    change inner ℂ (evenSineFactor • (fourierBasis (T := T) (2*((j+1:ℕ):ℤ))-
      fourierBasis (T := T) (-(2*((j+1:ℕ):ℤ))))) f = v j at h
    rw [inner_smul_left,inner_sub_left] at h
    simp only [← HilbertBasis.repr_apply_apply,fourierBasis_repr,hf.1] at h
    linear_combination evenSineFactor*h-
      fourierCoeff f (2*((j+1:ℕ):ℤ))*evenSineFactor_normalization
  apply circle_sine_fourier_ext T f _ _ hf.1 (circle_even_sine_coeff_neg T v)
    hf.2 (circle_even_sine_coeff_odd T v)
  intro j
  cases j with
  | zero =>
    have hz := hf.1 0
    simp only [neg_zero] at hz
    simp only [Nat.cast_zero,mul_zero,circle_even_sine_coeff_zero]
    linear_combination (1/2:ℂ)*hz
  | succ j => rw [circle_even_sine_coeff_pos,hc]

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = thetaParameter)

include hq hp he hqreal hpreal hs hc ho hr in
theorem circle_positive_rotation_sine_series :
    -circleUnitRotation T q p = circleEvenSineSynthesis T rotationSineSequence := by
  have hsector := circle_even_sine_sector_of_symmetries T (circleUnitRotation T q p)
    (circle_unit_rotation_reflect T q p hq hs)
    (circle_even_frequency_part_eq_self T _ (circle_unit_rotation_no_odd T q p hq ho))
  have hneg : InCircleEvenSineSector T (-circleUnitRotation T q p) := by
    simpa only [neg_one_smul] using circle_even_sine_sector_smul T (-1) _ hsector
  apply sine_reconstruction T _ hneg
  intro j
  exact circle_sine_mode_positive_rotation_pairing T q p hq hp he hqreal hpreal hs hc hr j

include hq hp he hqreal hpreal hs hc ho hr in
private theorem rotation_truncation_h4_error (N : ℕ) :
    circleAngularH4Norm T (-circleUnitRotationH4 T q p hq hp-
      circleSineTrialH4 T N (fun j => (rotationSineCoefficient j.val:ℂ))) ≤
      (2*(H:ℝ)/rotationCoefficientNorm)*
        ∑ k : Fin 5, 2^k.val*(momentTail (k.val+2) qb (N+1):ℝ) := by
  have hseries : ((-circleUnitRotationH4 T q p hq hp : circleH4Domain T) : CircleL2 T) =
      circleEvenSineSynthesis T rotationSineSequence :=
    circle_positive_rotation_sine_series T q p hq hp he hqreal hpreal hs hc ho hr
  have hv (k : Fin 5) : Summable (fun n : ℕ => ‖rotationSineSequence n‖ *
      (2*(n+1:ℕ):ℝ)^k.val) := by
    simpa only [rotationSineSequence,Complex.norm_real,Real.norm_eq_abs,Nat.add_zero] using
      (rotation_sine_coefficient_tail k 0).1
  have h := circle_sine_truncation_h4_error T _ rotationSineSequence hseries hv N
  apply h.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  simpa only [rotationSineSequence,Complex.norm_real,Real.norm_eq_abs,mul_assoc] using
    (rotation_sine_coefficient_tail k N).2

include hq hp he hqreal hpreal hs hc ho hr in
theorem circle_rotation_truncation_h4_error (N : ℕ) (c : ℂ) :
    circleAngularH4Norm T (-circleUnitRotationH4 T q p hq hp-
      c • circleSineTrialH4 T N (fun j => (rotationSineCoefficient j.val:ℂ))) ≤
      (2*(H:ℝ)/rotationCoefficientNorm)*
        (∑ k : Fin 5, 2^k.val*(momentTail (k.val+2) qb (N+1):ℝ))+
      ‖1-c‖ * ∑ j : Fin N, |rotationSineCoefficient j.val| *
        ∑ k : Fin 5, (2*(j.val+1:ℕ):ℝ)^k.val := by
  have h := circle_sine_truncation_rescale_error T (-circleUnitRotationH4 T q p hq hp)
    N (fun j => (rotationSineCoefficient j.val:ℂ)) c
  simp only [Complex.norm_real,Real.norm_eq_abs] at h
  exact h.trans (add_le_add
    (rotation_truncation_h4_error T q p hq hp he hqreal hpreal hs hc ho hr N) le_rfl)

end Profile
end Lemniscate
