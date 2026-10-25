import Lemniscate.PeriodicNeutralTransform

/-! The paper's first antisymmetric Fourier vector and the positive common
phase of the normalized rotation. The anchor is a genuine unit H4 vector. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleHouseholderAnchor : CircleL2 T :=
  evenCosineFactor • (fourierBasis (T := T) 2-fourierBasis (T := T) (-2))

noncomputable def circleHouseholderAnchorH4 : circleH4Domain T :=
  evenCosineFactor • (⟨fourierBasis (T := T) 2, circle_fourier_mem_h4 T 2⟩-
    ⟨fourierBasis (T := T) (-2), circle_fourier_mem_h4 T (-2)⟩)

theorem circle_householder_anchor_h4_coe :
    (circleHouseholderAnchorH4 T : CircleL2 T) = circleHouseholderAnchor T := rfl

theorem circle_householder_anchor_fourier (n : ℤ) :
    fourierCoeff (circleHouseholderAnchor T) n =
      evenCosineFactor*((if n = 2 then 1 else 0)-(if n = -2 then 1 else 0)) := by
  rw [← fourierBasis_repr, HilbertBasis.repr_apply_apply]
  have hb := orthonormal_iff_ite.mp (fourierBasis (T := T)).orthonormal
  simp only [circleHouseholderAnchor, inner_smul_right, inner_sub_right, hb]

theorem circle_householder_anchor_no_odd (i : ℤ) :
    fourierCoeff (circleHouseholderAnchor T) (2*i+1) = 0 := by
  rw [circle_householder_anchor_fourier, if_neg (by omega : 2*i+1 ≠ 2),
    if_neg (by omega : 2*i+1 ≠ -2), sub_self, mul_zero]

theorem circle_householder_anchor_reflect :
    circleReflect T (circleHouseholderAnchor T) = -circleHouseholderAnchor T := by
  rw [circleHouseholderAnchor, circle_reflect_smul, circle_reflect_sub,
    circle_reflect_basis, circle_reflect_basis]
  norm_num only [neg_neg]
  module

theorem circle_householder_anchor_pairing (f : CircleL2 T) :
    inner ℂ (circleHouseholderAnchor T) f =
      evenCosineFactor*(fourierCoeff f 2-fourierCoeff f (-2)) := by
  have hb (n : ℤ) : inner ℂ (fourierBasis (T := T) n) f = fourierCoeff f n := by
    simpa only [HilbertBasis.repr_apply_apply] using fourierBasis_repr f n
  rw [circleHouseholderAnchor, inner_smul_left, evenCosineFactor_conj,
    inner_sub_left, hb, hb]

theorem circle_householder_anchor_unit :
    inner ℂ (circleHouseholderAnchor T) (circleHouseholderAnchor T) = 1 := by
  have hb := orthonormal_iff_ite.mp (fourierBasis (T := T)).orthonormal
  have hdiff : inner ℂ (fourierBasis (T := T) 2-fourierBasis (T := T) (-2))
      (fourierBasis (T := T) 2-fourierBasis (T := T) (-2)) = 2 := by
    simp only [inner_sub_left, inner_sub_right, hb]
    norm_num
  rw [circleHouseholderAnchor, inner_smul_left, inner_smul_right,
    evenCosineFactor_conj, hdiff, evenCosineFactor_normalization]

theorem circle_rotation_phase_first (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (h₂ : ℝ)
    (hc : fourierCoeff (q^2 : C(AddCircle T, ℂ)) 2 = (h₂ : ℂ)) :
    fourierCoeff ((-I) • circleContinuousL2 T (q*p)) 2 = ((2*Real.pi/T)*h₂ : ℝ) := by
  have hd := fourierCoeff_classical_deriv T (q^2) ((2:ℂ) • (q*p))
    (circle_profile_square_deriv T q p hq) 2
  rw [circle_continuous_fourier_smul, hc] at hd
  have hf : fourierCoeff (q*p) 2 = (circleFrequencyFactor T 2/2)*(h₂:ℂ) := by
    linear_combination (1/2:ℂ)*hd
  rw [circle_fourierCoeff_smul, circle_continuous_l2_fourier, hf]
  simp only [circleFrequencyFactor]
  push_cast
  ring_nf
  simp [Complex.I_sq]

theorem circle_unit_rotation_phase_first (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (h₂ : ℝ)
    (hc : fourierCoeff (q^2 : C(AddCircle T, ℂ)) 2 = (h₂ : ℂ)) :
    fourierCoeff ((-I) • circleUnitRotation T q p) 2 =
      ((‖circleContinuousL2 T (q*p)‖⁻¹*(2*Real.pi/T)*h₂ : ℝ) : ℂ) := by
  have hp : (-I) • circleUnitRotation T q p =
      ((‖circleContinuousL2 T (q*p)‖:ℂ)⁻¹) • ((-I) • circleContinuousL2 T (q*p)) := by
    rw [circleUnitRotation, smul_comm]
  rw [hp, circle_fourierCoeff_smul, circle_rotation_phase_first T q p hq h₂ hc]
  push_cast
  ring

theorem circle_unit_rotation_phase_anchor (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ i : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*i+1) = 0) :
    ∃ c : ℝ, 0 < c ∧
      inner ℂ (circleHouseholderAnchor T) ((-I) • circleUnitRotation T q p) = (c : ℂ) ∧
      inner ℂ ((-I) • circleUnitRotation T q p) (circleHouseholderAnchor T) = (c : ℂ) := by
  let b := circleContinuousL2 T (q*p)
  let c : ℝ := (1/Real.sqrt 2)*(2*(‖b‖⁻¹*(2*Real.pi/T)*evenCoefficient thetaParameter nome 1))
  have hn : 0 < ‖b‖ := norm_pos_iff.mpr (circle_profile_rotation_ne_zero T q p hq hs hc ho)
  have hT : 0 < T := Fact.out
  have hh₂ := theta_nome_first_sine_coefficient_pos
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hfirst : fourierCoeff (q^2 : C(AddCircle T, ℂ)) 2 =
      (evenCoefficient thetaParameter nome 1 : ℂ) := by
    simpa only [Nat.cast_one, mul_one, fourierCoefficient, if_false,
      show ¬(1:ℕ) = 0 by decide] using hc 1
  have hr := circle_unit_rotation_reflect T q p hq hs
  have hsector := circle_even_sine_sector_of_symmetries T (circleUnitRotation T q p) hr
    (circle_even_frequency_part_eq_self T _ (circle_unit_rotation_no_odd T q p hq ho))
  have hphase := circle_sine_phase_sector T _ hsector
  have hpair : inner ℂ (circleHouseholderAnchor T) ((-I) • circleUnitRotation T q p) = (c : ℂ) := by
    rw [circle_householder_anchor_pairing, hphase.1,
      circle_unit_rotation_phase_first T q p hq _ hfirst]
    dsimp [c, b, evenCosineFactor]
    push_cast
    ring
  refine ⟨c, hcpos, hpair, ?_⟩
  rw [← inner_conj_symm, hpair, Complex.conj_ofReal]

end Lemniscate
