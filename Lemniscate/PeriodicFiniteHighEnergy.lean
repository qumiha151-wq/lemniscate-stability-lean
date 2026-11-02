import Lemniscate.PeriodicFiniteNormalization
import Lemniscate.PeriodicHouseholderAnchor
import Lemniscate.NeutralHouseholder

/-! Finite changes of variables leave the high-frequency energy unchanged.
The invariance is used in the full even-frequency energy estimate. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleFiniteRotationPhase : circleH4Domain T :=
  I • circleRotationApproximation T

noncomputable def circleFiniteAdjointPhase : CircleL2 T :=
  I • (circleAdjointApproximation T : CircleL2 T)

noncomputable def circleFiniteTransformedOperator
    (A : circleH4Domain T →ₗ[ℂ] CircleL2 T) : circleH4Domain T →ₗ[ℂ] CircleL2 T where
  toFun f :=
    neutralHouseholder (circleFiniteRotationPhase T : CircleL2 T) (circleHouseholderAnchor T)
      (neutralTransform (circleFiniteRotationPhase T) (circleFiniteAdjointPhase T)
        (A (neutralTransformInvDomain (circleFiniteRotationPhase T) (circleFiniteAdjointPhase T)
          (neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T) f))))
  map_add' f g := by
    have h : neutralTransformInvDomain (circleFiniteRotationPhase T) (circleFiniteAdjointPhase T)
        (neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T) (f+g)) =
        neutralTransformInvDomain (circleFiniteRotationPhase T) (circleFiniteAdjointPhase T)
          (neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T) f)+
        neutralTransformInvDomain (circleFiniteRotationPhase T) (circleFiniteAdjointPhase T)
          (neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T) g) := by
      apply Subtype.ext
      simp only [neutral_transform_inv_domain_coe, neutral_householder_domain_coe,
        Submodule.coe_add, map_add]
    rw [h, map_add, map_add, map_add]
  map_smul' c f := by
    have h : neutralTransformInvDomain (circleFiniteRotationPhase T) (circleFiniteAdjointPhase T)
        (neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T) (c • f)) =
        c • neutralTransformInvDomain (circleFiniteRotationPhase T) (circleFiniteAdjointPhase T)
          (neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T) f) := by
      apply Subtype.ext
      simp only [neutral_transform_inv_domain_coe, neutral_householder_domain_coe,
        Submodule.coe_smul_of_tower, map_smul]
    change _ = c • _
    rw [h, map_smul, map_smul, map_smul]

private theorem sine_trial_high_pairing (v : Fin 15 → ℂ) (f : CircleL2 T)
    (hf : ∀ n : ℤ, |(n:ℝ)| < 32 → fourierCoeff f n = 0) :
    inner ℂ (circleSineTrialH4 T 15 v : CircleL2 T) f = 0 := by
  have hb (n : ℤ) : inner ℂ (fourierBasis (T := T) n) f = fourierCoeff f n := by
    simpa only [HilbertBasis.repr_apply_apply] using fourierBasis_repr f n
  have hj (j : Fin 15) : inner ℂ (circleSineH4 T j.val : CircleL2 T) f = 0 := by
    have hpos : |((2*((j.val+1:ℕ):ℤ):ℤ):ℝ)| < 32 := by
      have hj := j.isLt
      push_cast
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast (show 2*(j.val+1) < 32 by omega)
    have hneg : |((-(2*((j.val+1:ℕ):ℤ)):ℤ):ℝ)| < 32 := by
      simpa only [Int.cast_neg, abs_neg] using hpos
    change inner ℂ (evenSineFactor •
      (fourierBasis (T := T) (2*((j.val+1:ℕ):ℤ))-
        fourierBasis (T := T) (-(2*((j.val+1:ℕ):ℤ))))) f = 0
    rw [inner_smul_left, inner_sub_left, hb, hb, hf _ hpos, hf _ hneg]
    ring
  simp only [circleSineTrialH4, Submodule.coe_sum, Submodule.coe_smul_of_tower,
    sum_inner, inner_smul_left, hj, mul_zero, Finset.sum_const_zero]

theorem circle_finite_high_pairings (f : circleH4Domain T)
    (hf : ∀ n : ℤ, |(n:ℝ)| < 32 → fourierCoeff (f : CircleL2 T) n = 0) :
    inner ℂ (circleFiniteRotationPhase T : CircleL2 T) (f : CircleL2 T) = 0 ∧
    inner ℂ (circleFiniteAdjointPhase T) (f : CircleL2 T) = 0 ∧
    inner ℂ (circleHouseholderAnchor T) (f : CircleL2 T) = 0 := by
  have he : inner ℂ (circleFiniteRotationPhase T : CircleL2 T) (f : CircleL2 T) = 0 := by
    change inner ℂ (I • (circleRotationApproximation T : CircleL2 T)) (f : CircleL2 T) = 0
    rw [inner_smul_left]
    have h := sine_trial_high_pairing T (fun j => (CoarseArithmetic.rotationFiniteCoefficient j:ℂ))
      (f : CircleL2 T) hf
    change inner ℂ (circleRotationApproximation T : CircleL2 T) (f : CircleL2 T) = 0 at h
    rw [h, mul_zero]
  have hp : inner ℂ (circleFiniteAdjointPhase T) (f : CircleL2 T) = 0 := by
    rw [circleFiniteAdjointPhase, inner_smul_left]
    have h := sine_trial_high_pairing T (fun j => (CoarseArithmetic.adjointFiniteCoefficient j:ℂ))
      (f : CircleL2 T) hf
    change inner ℂ (circleAdjointApproximation T : CircleL2 T) (f : CircleL2 T) = 0 at h
    rw [h, mul_zero]
  have ha : inner ℂ (circleHouseholderAnchor T) (f : CircleL2 T) = 0 := by
    rw [circle_householder_anchor_pairing, hf 2 (by norm_num), hf (-2) (by norm_num)]
    ring
  exact ⟨he, hp, ha⟩

theorem circle_finite_transform_high_energy
    (A : circleH4Domain T →ₗ[ℂ] CircleL2 T) (f : circleH4Domain T)
    (hf : ∀ n : ℤ, |(n:ℝ)| < 32 → fourierCoeff (f : CircleL2 T) n = 0) :
    inner ℂ (f : CircleL2 T) (circleFiniteTransformedOperator T A f) =
      inner ℂ (f : CircleL2 T) (A f) := by
  rcases circle_finite_high_pairings T f hf with ⟨he, hp, ha⟩
  have hU : neutralHouseholderDomain (circleFiniteRotationPhase T)
      (circleHouseholderAnchorH4 T) f = f := by
    simp only [neutralHouseholderDomain, circle_householder_anchor_h4_coe,
      inner_add_left, he, ha, add_zero, mul_zero, zero_smul, sub_zero]
  have hT : neutralTransformInvDomain (circleFiniteRotationPhase T)
      (circleFiniteAdjointPhase T) f = f := by
    simp only [neutralTransformInvDomain, inner_sub_left, hp, he, sub_self, zero_smul, sub_zero]
  have hfe := inner_eq_zero_symm.mpr he
  have hfa := inner_eq_zero_symm.mpr ha
  change inner ℂ (f : CircleL2 T)
    (neutralHouseholder (circleFiniteRotationPhase T : CircleL2 T) (circleHouseholderAnchor T)
      (neutralTransform (circleFiniteRotationPhase T) (circleFiniteAdjointPhase T)
        (A (neutralTransformInvDomain (circleFiniteRotationPhase T) (circleFiniteAdjointPhase T)
          (neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T) f))))) = _
  rw [hU, hT, neutral_householder_apply,
    inner_sub_right, inner_smul_right, inner_add_right, hfe, hfa]
  simp only [add_zero, mul_zero, sub_zero]
  rw [neutral_transform_apply, inner_add_right, inner_smul_right, hfe, mul_zero, add_zero]

end Lemniscate
