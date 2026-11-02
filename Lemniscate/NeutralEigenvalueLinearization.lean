import Lemniscate.NeutralMode
import Mathlib.Analysis.Normed.Operator.Banach

/-! The normalized eigenvalue equation in Banach-space coordinates.
Its derivative is a bounded linear isomorphism once the already established
neutral-mode and rank-one solvability properties are supplied. No regularity
or norm estimate for the inverse coordinate map is assumed. -/
namespace Lemniscate
open scoped ComplexConjugate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

noncomputable def normalizedPencilLinearization (C R : E →L[ℂ] E) (e ψ : E) :
    (ℂ × E) →L[ℂ] (E × ℂ) :=
  ((C.comp (ContinuousLinearMap.snd ℂ ℂ E))-
    (ContinuousLinearMap.fst ℂ ℂ E).smulRight e).prod
      ((innerSL ℂ ψ).comp (R.comp (ContinuousLinearMap.snd ℂ ℂ E)))

theorem normalized_pencil_linearization_apply (C R : E →L[ℂ] E) (e ψ : E) (a : ℂ) (f : E) :
    normalizedPencilLinearization C R e ψ (a,f) = (C f-a • e,inner ℂ ψ (R f)) := rfl

theorem normalized_pencil_linearization_bijective (A : NeutralCoerciveOperator E) (ψ : E)
    (hnorm : inner ℂ ψ (A.neutral:E) = 1) (hψ : ∀ u : A.domain, inner ℂ ψ (A.op u) = 0)
    (hsolve : ∀ y : E, ∃ u : A.domain,
      inner ℂ (A.neutral:E) (u:E) • (A.neutral:E)-A.op u = y)
    (R C : E →L[ℂ] E) (RDom : E →ₗ[ℂ] A.domain)
    (hR : ∀ f : E, (RDom f:E) = R f) (hRbij : Function.Bijective RDom)
    (hC : ∀ f : E, C f = A.op (RDom f)) :
    Function.Bijective (normalizedPencilLinearization C R (A.neutral:E) ψ) := by
  have hker (v : ℂ × E)
      (hv : normalizedPencilLinearization C R (A.neutral:E) ψ v = 0) : v = 0 := by
    obtain ⟨a,f⟩ := v
    change (C f-a • (A.neutral:E),inner ℂ ψ (R f)) = (0,0) at hv
    have heq : C f-a • (A.neutral:E) = 0 := congrArg Prod.fst hv
    have hcon : inner ℂ ψ (R f) = 0 := congrArg Prod.snd hv
    have hφ := congrArg (fun u : E => inner ℂ ψ u) (sub_eq_zero.mp heq)
    rw [hC,hψ,inner_smul_right,hnorm,mul_one] at hφ
    have ha : a = 0 := hφ.symm
    have hCf : C f = 0 := by simpa only [ha,zero_smul,sub_zero] using heq
    have hu := A.kernel_is_neutral (RDom f) (by rw [← hC,hCf])
    have hucoe := congrArg (fun u : A.domain => (u:E)) hu
    change (RDom f:E) = inner ℂ (A.neutral:E) (RDom f:E) • (A.neutral:E) at hucoe
    have hφu : inner ℂ ψ (RDom f:E) = 0 := by rw [hR]; exact hcon
    have hscalar := congrArg (fun u : E => inner ℂ ψ u) hucoe
    rw [hφu,inner_smul_right,hnorm,mul_one] at hscalar
    rw [← hscalar,zero_smul] at hucoe
    have hU : RDom f = 0 := Subtype.ext hucoe
    have hf : f = 0 := hRbij.1 (by rw [hU,map_zero])
    exact Prod.ext ha hf
  constructor
  · intro v w hvw
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub,hvw,sub_self]
  · rintro ⟨g,s⟩
    obtain ⟨u,hu⟩ := hsolve (-g+inner ℂ ψ g • (A.neutral:E))
    have he := congrArg (fun y : E => inner ℂ ψ y) hu
    have hue : inner ℂ (A.neutral:E) (u:E) = 0 := by
      simpa only [inner_sub_right,inner_smul_right,hnorm,hψ,mul_one,sub_zero,
        inner_add_right,inner_neg_right,neg_add_cancel] using he
    have hAu : A.op u = g-inner ℂ ψ g • (A.neutral:E) := by
      have h := congrArg Neg.neg hu
      simp only [hue,zero_smul,zero_sub,neg_neg] at h
      calc
        _ = -(-g+inner ℂ ψ g • (A.neutral:E)) := h
        _ = _ := by module
    let v : A.domain := u+(s-inner ℂ ψ (u:E)) • A.neutral
    have hAv : A.op v = g-inner ℂ ψ g • (A.neutral:E) := by
      simp only [v,map_add,map_smul,A.kills_neutral,smul_zero,add_zero,hAu]
    have hφv : inner ℂ ψ (v:E) = s := by
      change inner ℂ ψ ((u:E)+(s-inner ℂ ψ (u:E)) • (A.neutral:E)) = s
      rw [inner_add_right,inner_smul_right,hnorm,mul_one]
      ring
    obtain ⟨f,hf⟩ := hRbij.2 v
    refine ⟨(-inner ℂ ψ g,f),?_⟩
    rw [normalized_pencil_linearization_apply]
    apply Prod.ext
    · rw [hC,hf,hAv]
      module
    · rw [← hR,hf]
      exact hφv

noncomputable def normalizedPencilLinearizationEquiv (A : NeutralCoerciveOperator E) (ψ : E)
    (hnorm : inner ℂ ψ (A.neutral:E) = 1) (hψ : ∀ u : A.domain, inner ℂ ψ (A.op u) = 0)
    (hsolve : ∀ y : E, ∃ u : A.domain,
      inner ℂ (A.neutral:E) (u:E) • (A.neutral:E)-A.op u = y)
    (R C : E →L[ℂ] E) (RDom : E →ₗ[ℂ] A.domain)
    (hR : ∀ f : E, (RDom f:E) = R f) (hRbij : Function.Bijective RDom)
    (hC : ∀ f : E, C f = A.op (RDom f)) : (ℂ × E) ≃L[ℂ] (E × ℂ) :=
  ContinuousLinearEquiv.ofBijective (normalizedPencilLinearization C R (A.neutral:E) ψ)
    (LinearMap.ker_eq_bot.mpr
      (normalized_pencil_linearization_bijective A ψ hnorm hψ hsolve R C RDom hR hRbij hC).1)
    (LinearMap.range_eq_top.mpr
      (normalized_pencil_linearization_bijective A ψ hnorm hψ hsolve R C RDom hR hRbij hC).2)

end Lemniscate
