import Lemniscate.PeriodicCoverFourier
import Lemniscate.PeriodicReflectionOperator

/-! Multiplication by a periodically extended coefficient respects Bloch
components. The proof uses Fourier modes and continuity, avoiding a general
infinite convolution theorem. -/
namespace Lemniscate
open Complex MeasureTheory

private theorem basis_fourier (T : ℝ) [Fact (0 < T)] (m n : ℤ) :
    fourierCoeff (fourierBasis (T := T) m) n = if n = m then 1 else 0 := by
  rw [← circle_continuous_l2_fourier_basis,circle_continuous_l2_fourier,circle_continuous_fourier_mode]

variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

theorem circle_cover_component_basis (M : ℕ) (hM : 0 < M) (j k : ℤ) :
    circleCoverComponent T S M hM j (fourierBasis (T := S) (circleCoverIndex M j k)) =
      fourierBasis (T := T) k := by
  apply circle_fourier_ext T
  intro n
  rw [circle_cover_component_fourier,basis_fourier,basis_fourier]
  simp only [(circle_cover_index_injective M hM j).eq_iff]

theorem circle_cover_component_basis_zero (M : ℕ) (hM : 0 < M) (j m : ℤ)
    (hm : ¬∃ k : ℤ, circleCoverIndex M j k = m) :
    circleCoverComponent T S M hM j (fourierBasis (T := S) m) = 0 := by
  apply circle_fourier_ext T
  intro n
  rw [circle_cover_component_fourier,basis_fourier,circle_fourierCoeff_zero,
    if_neg (fun h => hm ⟨n,h⟩)]

private theorem cover_multiply_basis (M : ℕ) (hM : 0 < M)
    (h : C(AddCircle T, ℂ)) (H : C(AddCircle S, ℂ))
    (hmulti : ∀ n : ℤ, fourierCoeff H ((M:ℤ)*n) = fourierCoeff h n)
    (hvanish : ∀ n : ℤ, ¬(M:ℤ) ∣ n → fourierCoeff H n = 0) (j m : ℤ) :
    circleCoverComponent T S M hM j (circleMultiplyL2 S H (fourierBasis (T := S) m)) =
      circleMultiplyL2 T h (circleCoverComponent T S M hM j (fourierBasis (T := S) m)) := by
  by_cases hm : ∃ k : ℤ, circleCoverIndex M j k = m
  · obtain ⟨k,rfl⟩ := hm
    apply circle_fourier_ext T
    intro n
    rw [circle_cover_component_fourier,circle_multiply_basis_fourier,
      circle_cover_component_basis,circle_multiply_basis_fourier]
    rw [show circleCoverIndex M j n-circleCoverIndex M j k = (M:ℤ)*(n-k) by
      unfold circleCoverIndex; ring,hmulti]
  · rw [circle_cover_component_basis_zero T S M hM j m hm,map_zero]
    apply circle_fourier_ext T
    intro n
    rw [circle_cover_component_fourier,circle_multiply_basis_fourier,circle_fourierCoeff_zero]
    apply hvanish
    rintro ⟨d,hd⟩
    apply hm
    refine ⟨n-d,?_⟩
    unfold circleCoverIndex at hd ⊢
    linear_combination hd

theorem circle_cover_multiply (M : ℕ) (hM : 0 < M)
    (h : C(AddCircle T, ℂ)) (H : C(AddCircle S, ℂ))
    (hmulti : ∀ n : ℤ, fourierCoeff H ((M:ℤ)*n) = fourierCoeff h n)
    (hvanish : ∀ n : ℤ, ¬(M:ℤ) ∣ n → fourierCoeff H n = 0)
    (j : ℤ) (f : CircleL2 S) :
    circleCoverComponent T S M hM j (circleMultiplyL2 S H f) =
      circleMultiplyL2 T h (circleCoverComponent T S M hM j f) := by
  let F := (circleCoverComponent T S M hM j).comp (circleMultiplyL2 S H)
  let G := (circleMultiplyL2 T h).comp (circleCoverComponent T S M hM j)
  have hb (m : ℤ) : F (fourierBasis (T := S) m) = G (fourierBasis (T := S) m) :=
    cover_multiply_basis T S M hM h H hmulti hvanish j m
  have hF := ((fourierBasis (T := S)).hasSum_repr f).mapL F
  have hG := ((fourierBasis (T := S)).hasSum_repr f).mapL G
  simp only [map_smul,hb] at hF
  simp only [map_smul] at hG
  exact hF.unique hG

end Lemniscate
