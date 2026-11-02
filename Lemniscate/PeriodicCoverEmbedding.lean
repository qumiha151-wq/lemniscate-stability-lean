import Lemniscate.PeriodicCoverMultiplication
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Lemniscate.PeriodicSkewEnergy

/-! Insert a short-period function into one Bloch component by taking the
Hilbert adjoint of Fourier sampling. No separate summability construction
or normalization constant is required. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate
variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

noncomputable def circleCoverEmbedding (M : ℕ) (hM : 0 < M) (j : ℤ) :
    CircleL2 T →L[ℂ] CircleL2 S := (circleCoverComponent T S M hM j).adjoint

theorem circle_cover_embedding_fourier_index (M : ℕ) (hM : 0 < M) (j : ℤ)
    (f : CircleL2 T) (n : ℤ) :
    fourierCoeff (circleCoverEmbedding T S M hM j f) (circleCoverIndex M j n) = fourierCoeff f n := by
  rw [← fourierBasis_repr,HilbertBasis.repr_apply_apply]
  change inner ℂ (fourierBasis (T := S) (circleCoverIndex M j n))
    ((circleCoverComponent T S M hM j).adjoint f) = _
  rw [ContinuousLinearMap.adjoint_inner_right,circle_cover_component_basis,
    ← HilbertBasis.repr_apply_apply,fourierBasis_repr]

theorem circle_cover_embedding_fourier_zero (M : ℕ) (hM : 0 < M) (j m : ℤ)
    (f : CircleL2 T) (hm : ¬∃ n : ℤ, circleCoverIndex M j n = m) :
    fourierCoeff (circleCoverEmbedding T S M hM j f) m = 0 := by
  rw [← fourierBasis_repr,HilbertBasis.repr_apply_apply]
  change inner ℂ (fourierBasis (T := S) m) ((circleCoverComponent T S M hM j).adjoint f) = 0
  rw [ContinuousLinearMap.adjoint_inner_right,circle_cover_component_basis_zero T S M hM j m hm,
    inner_zero_left]

theorem circle_cover_component_embedding (M : ℕ) (hM : 0 < M) (j : ℤ) (f : CircleL2 T) :
    circleCoverComponent T S M hM j (circleCoverEmbedding T S M hM j f) = f := by
  apply circle_fourier_ext T
  intro n
  rw [circle_cover_component_fourier,circle_cover_embedding_fourier_index]

theorem circle_cover_embedding_injective (M : ℕ) (hM : 0 < M) (j : ℤ) :
    Function.Injective (circleCoverEmbedding T S M hM j) := by
  intro f g h
  have heq := congrArg (circleCoverComponent T S M hM j) h
  simpa only [circle_cover_component_embedding] using heq

theorem circle_cover_embedding_multiply (M : ℕ) (hM : 0 < M)
    (h : C(AddCircle T, ℂ)) (H : C(AddCircle S, ℂ))
    (hreal : ∀ x, conj (h x) = h x) (Hreal : ∀ x, conj (H x) = H x)
    (hmulti : ∀ n : ℤ, fourierCoeff H ((M:ℤ)*n) = fourierCoeff h n)
    (hvanish : ∀ n : ℤ, ¬(M:ℤ) ∣ n → fourierCoeff H n = 0)
    (j : ℤ) (f : CircleL2 T) :
    circleMultiplyL2 S H (circleCoverEmbedding T S M hM j f) =
      circleCoverEmbedding T S M hM j (circleMultiplyL2 T h f) := by
  apply ext_inner_right ℂ
  intro g
  change inner ℂ (circleMultiplyL2 S H ((circleCoverComponent T S M hM j).adjoint f)) g =
    inner ℂ ((circleCoverComponent T S M hM j).adjoint (circleMultiplyL2 T h f)) g
  rw [circle_multiply_l2_symmetric S H Hreal,ContinuousLinearMap.adjoint_inner_left,
    circle_cover_multiply T S M hM h H hmulti hvanish,
    ← circle_multiply_l2_symmetric T h hreal,ContinuousLinearMap.adjoint_inner_left]

end Lemniscate
