import Lemniscate.PeriodicCoverEmbeddingH4
import Lemniscate.PeriodicCoverCoefficientData

/-! Lifting an actual short-period Bloch eigenfunction gives an eigenfunction
of the actual long-period differential operator. Only extension data for the
original coefficient are needed; its derivative data are derived. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate
variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

theorem circle_cover_embedding_operator (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T)
    (h h₁ h₂ : C(AddCircle T, ℂ)) (H H₁ H₂ : C(AddCircle S, ℂ))
    (hd : HasCircleDeriv T h h₁) (hd₁ : HasCircleDeriv T h₁ h₂)
    (hD : HasCircleDeriv S H H₁) (hD₁ : HasCircleDeriv S H₁ H₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (Hreal : ∀ x, conj (H x) = H x) (H₁real : ∀ x, conj (H₁ x) = H₁ x)
    (H₂real : ∀ x, conj (H₂ x) = H₂ x)
    (hmulti : ∀ n : ℤ, fourierCoeff H ((M:ℤ)*n) = fourierCoeff h n)
    (hvanish : ∀ n : ℤ, ¬(M:ℤ) ∣ n → fourierCoeff H n = 0)
    (j : ℤ) (f : circleH4Domain T) :
    circleH4Operator S H H₁ H₂ (circleCoverEmbeddingH4 T S M hM hS j f) =
      circleCoverEmbedding T S M hM j
        (circleBlochOperator T h h₁ h₂ ((j:ℝ)/(M:ℝ)) f) := by
  obtain ⟨hmulti₁,hvanish₁⟩ := circle_cover_derivative_coefficients T S M hM hS
    h h₁ H H₁ hd hD hmulti hvanish
  obtain ⟨hmulti₂,hvanish₂⟩ := circle_cover_derivative_coefficients T S M hM hS
    h₁ h₂ H₁ H₂ hd₁ hD₁ hmulti₁ hvanish₁
  simp only [circle_h4_operator_expanded,circle_cover_embedding_h4_jet,
    circleCoverEmbeddingJet,circle_cover_embedding_h4_coe,
    circleBlochOperator,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    LinearMap.comp_apply,Submodule.subtype_apply,map_add,map_sub,map_smul,
    circle_cover_embedding_multiply T S M hM h H hreal Hreal hmulti hvanish,
    circle_cover_embedding_multiply T S M hM h₁ H₁ h₁real H₁real hmulti₁ hvanish₁,
    circle_cover_embedding_multiply T S M hM h₂ H₂ h₂real H₂real hmulti₂ hvanish₂]
  rfl

end Lemniscate
