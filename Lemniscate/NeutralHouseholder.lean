import Lemniscate.NeutralTransform

/-! The exact Householder change used after removal of the neutral factors.
The unit vectors and real symmetric cross pairing are explicit inputs. -/
namespace Lemniscate
open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (e a : E)

noncomputable def neutralHouseholder : E →L[ℂ] E :=
  ContinuousLinearMap.id ℂ E -
    (1+inner ℂ e a)⁻¹ • InnerProductSpace.rankOne ℂ (e+a) (e+a)

theorem neutral_householder_apply (f : E) :
    neutralHouseholder e a f = f-((1+inner ℂ e a)⁻¹*inner ℂ (e+a) f) • (e+a) := by
  simp only [neutralHouseholder, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply, smul_smul]

theorem neutral_householder_sum_inner (he : inner ℂ e e = 1) (ha : inner ℂ a a = 1)
    (hea : inner ℂ a e = inner ℂ e a) :
    inner ℂ (e+a) (e+a) = 2*(1+inner ℂ e a) := by
  rw [inner_add_left, inner_add_right, inner_add_right, he, ha, hea]
  ring

theorem neutral_householder_sum_pairing (he : inner ℂ e e = 1) (ha : inner ℂ a a = 1)
    (hea : inner ℂ a e = inner ℂ e a) (hd : 1+inner ℂ e a ≠ 0) (f : E) :
    inner ℂ (e+a) (neutralHouseholder e a f) = -inner ℂ (e+a) f := by
  rw [neutral_householder_apply, inner_sub_right, inner_smul_right,
    neutral_householder_sum_inner e a he ha hea]
  field_simp [hd]
  ring

theorem neutral_householder_involutive (he : inner ℂ e e = 1) (ha : inner ℂ a a = 1)
    (hea : inner ℂ a e = inner ℂ e a) (hd : 1+inner ℂ e a ≠ 0) (f : E) :
    neutralHouseholder e a (neutralHouseholder e a f) = f := by
  rw [neutral_householder_apply, neutral_householder_sum_pairing e a he ha hea hd,
    neutral_householder_apply, mul_neg, neg_smul]
  abel

theorem neutral_householder_anchor (ha : inner ℂ a a = 1)
    (hd : 1+inner ℂ e a ≠ 0) : neutralHouseholder e a a = -e := by
  rw [neutral_householder_apply, inner_add_left, ha,
    show inner ℂ e a+1 = 1+inner ℂ e a by ring, inv_mul_cancel₀ hd, one_smul]
  abel

theorem neutral_householder_selfadjoint (hea : inner ℂ a e = inner ℂ e a) (f g : E) :
    inner ℂ (neutralHouseholder e a f) g = inner ℂ f (neutralHouseholder e a g) := by
  have hd : conj (1+inner ℂ e a) = 1+inner ℂ e a := by
    rw [map_add, map_one, inner_conj_symm, hea]
  rw [neutral_householder_apply, neutral_householder_apply, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, map_mul, map_inv₀, hd,
    inner_conj_symm]
  ring

theorem neutral_householder_inner (he : inner ℂ e e = 1) (ha : inner ℂ a a = 1)
    (hea : inner ℂ a e = inner ℂ e a) (hd : 1+inner ℂ e a ≠ 0) (f g : E) :
    inner ℂ (neutralHouseholder e a f) (neutralHouseholder e a g) = inner ℂ f g := by
  rw [neutral_householder_selfadjoint e a hea, neutral_householder_involutive e a he ha hea hd]

theorem neutral_householder_norm (he : inner ℂ e e = 1) (ha : inner ℂ a a = 1)
    (hea : inner ℂ a e = inner ℂ e a) (hd : 1+inner ℂ e a ≠ 0) (f : E) :
    ‖neutralHouseholder e a f‖ = ‖f‖ := by
  have hn : ‖neutralHouseholder e a f‖^2 = ‖f‖^2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
      neutral_householder_inner e a he ha hea hd]
  nlinarith [norm_nonneg f, norm_nonneg (neutralHouseholder e a f)]

noncomputable def neutralHouseholderDomain {D : Submodule ℂ E} (e a f : D) : D :=
  f-((1+inner ℂ (e : E) (a : E))⁻¹*inner ℂ ((e : E)+(a : E)) (f : E)) • (e+a)

theorem neutral_householder_domain_coe {D : Submodule ℂ E} (e a f : D) :
    (neutralHouseholderDomain e a f : E) = neutralHouseholder (e : E) (a : E) (f : E) := by
  simp only [neutralHouseholderDomain, Submodule.coe_sub, Submodule.coe_smul,
    Submodule.coe_add, neutral_householder_apply]

theorem neutral_householder_domain_involutive {D : Submodule ℂ E} (e a : D)
    (he : inner ℂ (e : E) (e : E) = 1) (ha : inner ℂ (a : E) (a : E) = 1)
    (hea : inner ℂ (a : E) (e : E) = inner ℂ (e : E) (a : E))
    (hd : 1+inner ℂ (e : E) (a : E) ≠ 0) (f : D) :
    neutralHouseholderDomain e a (neutralHouseholderDomain e a f) = f := by
  apply Subtype.ext
  rw [neutral_householder_domain_coe, neutral_householder_domain_coe]
  exact neutral_householder_involutive (e : E) (a : E) he ha hea hd (f : E)

end Lemniscate
