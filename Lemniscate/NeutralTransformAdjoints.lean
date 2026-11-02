import Lemniscate.NeutralHouseholder

/-! Adjoint changes of variables preserve the explicit linear domain.
These pairing identities require no maximal unbounded-adjoint theorem. -/
namespace Lemniscate
open Complex
open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {D : Submodule ℂ E}

noncomputable def neutralTransformAdjointDomain (e ψ : D) : D →ₗ[ℂ] D where
  toFun f := f+inner ℂ (e:E) (f:E) • (ψ-e)
  map_add' f g := by
    simp only [Submodule.coe_add, inner_add_right, add_smul]
    module
  map_smul' c f := by
    change _ = c • _
    simp only [Submodule.coe_smul_of_tower, inner_smul_right]
    module

noncomputable def neutralHouseholderAdjointDomain (e a : D) : D →ₗ[ℂ] D where
  toFun f := f-(conj (1+inner ℂ (e:E) (a:E))⁻¹*
    inner ℂ ((e:E)+(a:E)) (f:E)) • (e+a)
  map_add' f g := by
    simp only [Submodule.coe_add, inner_add_right, mul_add, add_smul]
    module
  map_smul' c f := by
    change _ = c • _
    simp only [Submodule.coe_smul_of_tower, inner_smul_right]
    module

theorem neutral_transform_adjoint_domain_green (e ψ f : D) (g : E) :
    inner ℂ (neutralTransformAdjointDomain e ψ f:E) g =
      inner ℂ (f:E) (neutralTransform e (ψ:E) g) := by
  change inner ℂ ((f:E)+inner ℂ (e:E) (f:E) • ((ψ:E)-(e:E))) g = _
  simp only [neutral_transform_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

theorem neutral_householder_adjoint_domain_green (e a f : D) (g : E) :
    inner ℂ (neutralHouseholderAdjointDomain e a f:E) g =
      inner ℂ (f:E) (neutralHouseholder (e:E) (a:E) g) := by
  change inner ℂ ((f:E)-(conj (1+inner ℂ (e:E) (a:E))⁻¹*
    inner ℂ ((e:E)+(a:E)) (f:E)) • ((e:E)+(a:E))) g = _
  simp only [neutral_householder_apply, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, map_mul, map_inv₀, conj_conj, inner_conj_symm]
  ring

end Lemniscate
