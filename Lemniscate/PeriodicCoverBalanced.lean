import Lemniscate.PeriodicCoverParseval
import Lemniscate.PeriodicCoverComponents

/-! Balanced representatives of the finite Bloch residue classes. Moving a
representative by M changes the sampled short-period function but leaves its
lifted projection unchanged. This gives full reconstruction and Parseval for
the signed Bloch parameters without introducing a gauge-change operator.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped BigOperators

def circleCoverBalancedIndex (M : ℕ) (j : Fin M) : ℤ :=
  if 2*j.val ≤ M then (j.val:ℤ) else (j.val:ℤ)-(M:ℤ)

variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

/-- A change of integer representative leaves the actual residue projection
on the long circle unchanged. -/
theorem circle_cover_projection_sub_period (M : ℕ) (hM : 0 < M) (j : ℤ)
    (f : CircleL2 S) :
    circleCoverEmbedding T S M hM (j-(M:ℤ))
        (circleCoverComponent T S M hM (j-(M:ℤ)) f) =
      circleCoverEmbedding T S M hM j (circleCoverComponent T S M hM j f) := by
  apply circle_fourier_ext S
  intro n
  by_cases hn : ∃ m : ℤ, circleCoverIndex M j m = n
  · obtain ⟨m,rfl⟩ := hn
    have hindex : circleCoverIndex M (j-(M:ℤ)) (m+1) = circleCoverIndex M j m := by
      dsimp only [circleCoverIndex]
      ring
    have hleft := circle_cover_embedding_fourier_index T S M hM (j-(M:ℤ))
      (circleCoverComponent T S M hM (j-(M:ℤ)) f) (m+1)
    rw [circle_cover_component_fourier,hindex] at hleft
    have hright := circle_cover_embedding_fourier_index T S M hM j
      (circleCoverComponent T S M hM j f) m
    rw [circle_cover_component_fourier] at hright
    exact hleft.trans hright.symm
  · have hn' : ¬∃ m : ℤ, circleCoverIndex M (j-(M:ℤ)) m = n := by
      rintro ⟨m,hm⟩
      apply hn
      refine ⟨m-1,?_⟩
      calc
        circleCoverIndex M j (m-1) = circleCoverIndex M (j-(M:ℤ)) m := by
          dsimp only [circleCoverIndex]
          ring
        _ = n := hm
    rw [circle_cover_embedding_fourier_zero T S M hM (j-(M:ℤ)) n _ hn',
      circle_cover_embedding_fourier_zero T S M hM j n _ hn]

/-- Reconstruction and exact Parseval with the signed residue representatives. -/
theorem circle_cover_balanced_reconstruction_parseval (M : ℕ) (hM : 0 < M)
    (f : CircleL2 S) :
    f = ∑ j : Fin M, circleCoverEmbedding T S M hM (circleCoverBalancedIndex M j)
        (circleCoverComponent T S M hM (circleCoverBalancedIndex M j) f) ∧
      ‖f‖^2 = ∑ j : Fin M,
        ‖circleCoverComponent T S M hM (circleCoverBalancedIndex M j) f‖^2 := by
  classical
  obtain ⟨hreconstruct,hparseval⟩ := circle_cover_reconstruction_parseval T S M hM f
  have hprojection (j : Fin M) :
      circleCoverEmbedding T S M hM (circleCoverBalancedIndex M j)
          (circleCoverComponent T S M hM (circleCoverBalancedIndex M j) f) =
        circleCoverEmbedding T S M hM (j.val:ℤ)
          (circleCoverComponent T S M hM (j.val:ℤ) f) := by
    dsimp only [circleCoverBalancedIndex]
    split_ifs with h
    · rfl
    · exact circle_cover_projection_sub_period T S M hM (j.val:ℤ) f
  have hnorm (j : Fin M) :
      ‖circleCoverComponent T S M hM (circleCoverBalancedIndex M j) f‖^2 =
        ‖circleCoverComponent T S M hM (j.val:ℤ) f‖^2 := by
    have hinner :
        inner ℂ (circleCoverComponent T S M hM (circleCoverBalancedIndex M j) f)
            (circleCoverComponent T S M hM (circleCoverBalancedIndex M j) f) =
          inner ℂ (circleCoverComponent T S M hM (j.val:ℤ) f)
            (circleCoverComponent T S M hM (j.val:ℤ) f) := by
      rw [← circle_cover_embedding_inner T S M hM (circleCoverBalancedIndex M j) _ f,
        hprojection,circle_cover_embedding_inner]
    rw [norm_sq_eq_re_inner (𝕜 := ℂ),norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact congrArg Complex.re hinner
  constructor
  · calc
      f = ∑ j : Fin M, circleCoverEmbedding T S M hM (j.val:ℤ)
          (circleCoverComponent T S M hM (j.val:ℤ) f) := hreconstruct
      _ = _ := Finset.sum_congr rfl (fun j _ => (hprojection j).symm)
  · calc
      ‖f‖^2 = ∑ j : Fin M, ‖circleCoverComponent T S M hM (j.val:ℤ) f‖^2 := hparseval
      _ = _ := Finset.sum_congr rfl (fun j _ => (hnorm j).symm)

/-- All signed Bloch parameters lie in the centered half interval. Every
nonzero residue is separated from zero by at least one inverse cover length. -/
theorem circle_cover_balanced_parameter_bounds (M : ℕ) (hM : 0 < M) (j : Fin M) :
    |((circleCoverBalancedIndex M j:ℝ)/(M:ℝ))| ≤ 1/2 ∧
      (j.val ≠ 0 → 1/(M:ℝ) ≤ |((circleCoverBalancedIndex M j:ℝ)/(M:ℝ))|) := by
  have hj0 : (0:ℤ) ≤ (j.val:ℤ) := Int.natCast_nonneg _
  have hjM : (j.val:ℤ) < (M:ℤ) := by exact_mod_cast j.isLt
  have hbalanced : 2*|circleCoverBalancedIndex M j| ≤ (M:ℤ) := by
    dsimp only [circleCoverBalancedIndex]
    split_ifs with h
    · rw [abs_of_nonneg hj0]
      exact_mod_cast h
    · rw [abs_of_neg (by omega : (j.val:ℤ)-(M:ℤ) < 0)]
      omega
  refine ⟨circle_cover_parameter_bound M hM (circleCoverBalancedIndex M j) hbalanced,?_⟩
  intro hj
  have hne : circleCoverBalancedIndex M j ≠ 0 := by
    dsimp only [circleCoverBalancedIndex]
    split_ifs with h
    · exact_mod_cast hj
    · omega
  have hdist : (1:ℤ) ≤ |circleCoverBalancedIndex M j| := by
    have hpos := abs_pos.mpr hne
    omega
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  rw [abs_div,abs_of_pos hMr]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hdist) hMr.le

end Lemniscate
