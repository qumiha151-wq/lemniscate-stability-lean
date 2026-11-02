import Lemniscate.PeriodicCoverEmbedding
import Lemniscate.PeriodicCoverH4
import Lemniscate.PeriodicBlochGarding

/-! A short-period H4 function lifts into one Bloch component of the actual
long-period H4 domain. The existing shifted weak derivative chain supplies
all four long-period derivatives, without new Sobolev norm estimates. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

theorem circle_cover_embedding_weak_deriv (M : ℕ) (hM : 0 < M)
    (hS : S = (M:ℝ)*T) (j : ℤ) (f g : CircleL2 T)
    (hg : HasWeakCircleShiftedDeriv T
      ((((j:ℝ)/(M:ℝ):ℝ):ℂ)*circleFrequencyFactor T 1) f g) :
    HasWeakCircleDeriv S (circleCoverEmbedding T S M hM j f)
      (circleCoverEmbedding T S M hM j g) := by
  apply weak_circle_deriv_of_fourier
  intro m
  by_cases hm : ∃ n : ℤ, circleCoverIndex M j n = m
  · obtain ⟨n,rfl⟩ := hm
    rw [circle_cover_embedding_fourier_index,circle_cover_embedding_fourier_index,
      circle_shifted_deriv_fourier T _ _ _ hg,circle_cover_frequency T S M hM hS j n]
  · rw [circle_cover_embedding_fourier_zero T S M hM j m g hm,
      circle_cover_embedding_fourier_zero T S M hM j m f hm,mul_zero]

noncomputable def circleCoverEmbeddingJet (M : ℕ) (hM : 0 < M)
    (hS : S = (M:ℝ)*T) (j : ℤ) (f : circleH4Domain T) :
    CircleH4Jet S (circleCoverEmbedding T S M hM j (f:CircleL2 T)) := by
  let z : ℂ := (((j:ℝ)/(M:ℝ):ℝ):ℂ)*circleFrequencyFactor T 1
  let E := circleCoverEmbedding T S M hM j
  have hc := circle_h4_shifted_derivative_chain T z f
  exact ⟨E (circleShiftedFirst T z f),E (circleShiftedSecond T z f),
    E (circleShiftedThird T z f),E (circleShiftedFourth T z f),
    circle_cover_embedding_weak_deriv T S M hM hS j _ _ hc.1,
    circle_cover_embedding_weak_deriv T S M hM hS j _ _ hc.2.1,
    circle_cover_embedding_weak_deriv T S M hM hS j _ _ hc.2.2.1,
    circle_cover_embedding_weak_deriv T S M hM hS j _ _ hc.2.2.2⟩

theorem circle_cover_embedding_mem_h4 (M : ℕ) (hM : 0 < M)
    (hS : S = (M:ℝ)*T) (j : ℤ) (f : circleH4Domain T) :
    InCircleH4 S (circleCoverEmbedding T S M hM j (f:CircleL2 T)) := by
  let J := circleCoverEmbeddingJet T S M hM hS j f
  exact ⟨J.first,J.second,J.third,J.fourth,J.hfirst,J.hsecond,J.hthird,J.hfourth⟩

noncomputable def circleCoverEmbeddingH4 (M : ℕ) (hM : 0 < M)
    (hS : S = (M:ℝ)*T) (j : ℤ) (f : circleH4Domain T) : circleH4Domain S :=
  ⟨circleCoverEmbedding T S M hM j (f:CircleL2 T),
    circle_cover_embedding_mem_h4 T S M hM hS j f⟩

theorem circle_cover_embedding_h4_coe (M : ℕ) (hM : 0 < M)
    (hS : S = (M:ℝ)*T) (j : ℤ) (f : circleH4Domain T) :
    (circleCoverEmbeddingH4 T S M hM hS j f:CircleL2 S) =
      circleCoverEmbedding T S M hM j (f:CircleL2 T) := rfl

theorem circle_cover_embedding_h4_jet (M : ℕ) (hM : 0 < M)
    (hS : S = (M:ℝ)*T) (j : ℤ) (f : circleH4Domain T) :
    circleH4Jet S (circleCoverEmbeddingH4 T S M hM hS j f) =
      circleCoverEmbeddingJet T S M hM hS j f := circle_h4_jet_unique S _ _ _

end Lemniscate
