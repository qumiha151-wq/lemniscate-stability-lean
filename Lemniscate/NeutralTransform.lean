import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.Module

/-! The exact bounded neutral change of variables and its inverse, on an
explicit linear domain. Its conjugated operator is the orthogonal compression
when the exact kernel and adjoint-kernel identities hold. -/
namespace Lemniscate
open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {D : Submodule ℂ E} (e : D) (ψ : E)

noncomputable def neutralTransform : E →L[ℂ] E :=
  ContinuousLinearMap.id ℂ E + InnerProductSpace.rankOne ℂ (e : E) (ψ-(e : E))

noncomputable def neutralTransformInv : E →L[ℂ] E :=
  ContinuousLinearMap.id ℂ E - InnerProductSpace.rankOne ℂ (e : E) (ψ-(e : E))

theorem neutral_transform_apply (f : E) :
    neutralTransform e ψ f = f+inner ℂ (ψ-(e : E)) f • (e : E) := rfl

theorem neutral_transform_inv_apply (f : E) :
    neutralTransformInv e ψ f = f-inner ℂ (ψ-(e : E)) f • (e : E) := rfl

theorem neutral_remainder_pairing (hunit : inner ℂ (e : E) (e : E) = 1)
    (hnorm : inner ℂ ψ (e : E) = 1) : inner ℂ (ψ-(e : E)) (e : E) = 0 := by
  rw [inner_sub_left, hnorm, hunit, sub_self]

theorem neutral_transform_right_inverse (hunit : inner ℂ (e : E) (e : E) = 1)
    (hnorm : inner ℂ ψ (e : E) = 1) (f : E) :
    neutralTransform e ψ (neutralTransformInv e ψ f) = f := by
  simp only [neutral_transform_apply, neutral_transform_inv_apply, inner_sub_right,
    inner_smul_right, neutral_remainder_pairing e ψ hunit hnorm, mul_zero, sub_zero]
  abel

theorem neutral_transform_left_inverse (hunit : inner ℂ (e : E) (e : E) = 1)
    (hnorm : inner ℂ ψ (e : E) = 1) (f : E) :
    neutralTransformInv e ψ (neutralTransform e ψ f) = f := by
  simp only [neutral_transform_apply, neutral_transform_inv_apply, inner_add_right,
    inner_smul_right, neutral_remainder_pairing e ψ hunit hnorm, mul_zero, add_zero]
  abel

noncomputable def neutralTransformDomain (f : D) : D :=
  f+inner ℂ (ψ-(e : E)) (f : E) • e

noncomputable def neutralTransformInvDomain (f : D) : D :=
  f-inner ℂ (ψ-(e : E)) (f : E) • e

theorem neutral_transform_domain_coe (f : D) :
    (neutralTransformDomain e ψ f : E) = neutralTransform e ψ (f : E) := rfl

theorem neutral_transform_inv_domain_coe (f : D) :
    (neutralTransformInvDomain e ψ f : E) = neutralTransformInv e ψ (f : E) := rfl

theorem neutral_transform_domain_right_inverse (hunit : inner ℂ (e : E) (e : E) = 1)
    (hnorm : inner ℂ ψ (e : E) = 1) (f : D) :
    neutralTransformDomain e ψ (neutralTransformInvDomain e ψ f) = f := by
  apply Subtype.ext
  exact neutral_transform_right_inverse e ψ hunit hnorm (f : E)

theorem neutral_transform_domain_left_inverse (hunit : inner ℂ (e : E) (e : E) = 1)
    (hnorm : inner ℂ ψ (e : E) = 1) (f : D) :
    neutralTransformInvDomain e ψ (neutralTransformDomain e ψ f) = f := by
  apply Subtype.ext
  exact neutral_transform_left_inverse e ψ hunit hnorm (f : E)

theorem neutral_transform_pairing (hunit : inner ℂ (e : E) (e : E) = 1) (f : E) :
    inner ℂ (e : E) (neutralTransform e ψ f) = inner ℂ ψ f := by
  rw [neutral_transform_apply, inner_add_right, inner_smul_right, hunit, mul_one,
    inner_sub_left]
  ring

theorem neutral_transformed_operator (A : D →ₗ[ℂ] E) (he : A e = 0)
    (hψ : ∀ f : D, inner ℂ ψ (A f) = 0) (f : D) :
    neutralTransform e ψ (A (neutralTransformInvDomain e ψ f)) =
      A f-inner ℂ (e : E) (A f) • (e : E) := by
  rw [neutralTransformInvDomain, map_sub, map_smul, he, smul_zero, sub_zero,
    neutral_transform_apply, inner_sub_left, hψ, zero_sub, neg_smul]
  rw [sub_eq_add_neg]

theorem neutral_transformed_operator_orthogonal (hunit : inner ℂ (e : E) (e : E) = 1)
    (A : D →ₗ[ℂ] E) (he : A e = 0) (hψ : ∀ f : D, inner ℂ ψ (A f) = 0) (f : D) :
    inner ℂ (e : E) (neutralTransform e ψ (A (neutralTransformInvDomain e ψ f))) = 0 := by
  rw [neutral_transformed_operator e ψ A he hψ, inner_sub_right, inner_smul_right,
    hunit, mul_one, sub_self]

theorem neutral_transformed_operator_neutral (A : D →ₗ[ℂ] E) (he : A e = 0)
    (hψ : ∀ f : D, inner ℂ ψ (A f) = 0) :
    neutralTransform e ψ (A (neutralTransformInvDomain e ψ e)) = 0 := by
  rw [neutral_transformed_operator e ψ A he hψ, he, inner_zero_right, zero_smul, sub_zero]

end Lemniscate
