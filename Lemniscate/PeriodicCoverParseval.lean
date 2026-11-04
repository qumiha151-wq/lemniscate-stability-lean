import Lemniscate.PeriodicCoverEmbedding

/-! Reconstruction and Parseval for all L2 functions from the finitely many
residue Bloch components. Both circle spaces use normalized Haar measure.
The canonical lift is already the Hilbert adjoint of component sampling.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped BigOperators ComplexConjugate

private theorem circle_cover_index_fin_emod (M : ℕ) (j : Fin M) (n : ℤ) :
    circleCoverIndex M (j.val:ℤ) n % (M:ℤ) = (j.val:ℤ) := by
  dsimp only [circleCoverIndex]
  rw [Int.mul_add_emod_self_left]
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast j.isLt)

variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

/-- This is the defining Hilbert-adjoint identity of the existing lift. -/
theorem circle_cover_embedding_inner (M : ℕ) (hM : 0 < M) (j : ℤ)
    (g : CircleL2 T) (f : CircleL2 S) :
    inner ℂ (circleCoverEmbedding T S M hM j g) f =
      inner ℂ g (circleCoverComponent T S M hM j f) :=
  (circleCoverComponent T S M hM j).adjoint_inner_left f g

/-- Every long-circle L2 function is the finite sum of its lifted residue
components, and the squared component norms sum exactly to its squared norm.
No factor M occurs because both Fourier bases use mass-one Haar measure.
The statements only use the canonical Fourier maps; the period relation
S=M*T is needed for differential-operator intertwining, not for this identity. -/
theorem circle_cover_reconstruction_parseval (M : ℕ) (hM : 0 < M)
    (f : CircleL2 S) :
    f = ∑ j : Fin M, circleCoverEmbedding T S M hM (j.val:ℤ)
        (circleCoverComponent T S M hM (j.val:ℤ) f) ∧
      ‖f‖^2 = ∑ j : Fin M, ‖circleCoverComponent T S M hM (j.val:ℤ) f‖^2 := by
  classical
  have hreconstruct :
      f = ∑ j : Fin M, circleCoverEmbedding T S M hM (j.val:ℤ)
        (circleCoverComponent T S M hM (j.val:ℤ) f) := by
    apply circle_fourier_ext S
    intro n
    have hMZ : (0:ℤ) < M := by exact_mod_cast hM
    have hr0 : 0 ≤ n % (M:ℤ) := Int.emod_nonneg n (ne_of_gt hMZ)
    have hrM : n % (M:ℤ) < (M:ℤ) := Int.emod_lt_of_pos n hMZ
    let j : Fin M := ⟨(n % (M:ℤ)).toNat,(Int.toNat_lt hr0).mpr hrM⟩
    have hj : (j.val:ℤ) = n % (M:ℤ) := Int.toNat_of_nonneg hr0
    have hindex : circleCoverIndex M (j.val:ℤ) (n/(M:ℤ)) = n := by
      dsimp only [circleCoverIndex]
      rw [hj]
      exact Int.mul_ediv_add_emod n (M:ℤ)
    have hmain :
        fourierCoeff (circleCoverEmbedding T S M hM (j.val:ℤ)
          (circleCoverComponent T S M hM (j.val:ℤ) f)) n = fourierCoeff f n := by
      have h := circle_cover_embedding_fourier_index T S M hM (j.val:ℤ)
        (circleCoverComponent T S M hM (j.val:ℤ) f) (n/(M:ℤ))
      rw [circle_cover_component_fourier,hindex] at h
      exact h
    have hdisjoint (k : Fin M) (hkj : k ≠ j) :
        ¬∃ m : ℤ, circleCoverIndex M (k.val:ℤ) m = n := by
      rintro ⟨m,hm⟩
      have hmod := congrArg (fun z : ℤ => z % (M:ℤ)) hm
      rw [circle_cover_index_fin_emod] at hmod
      have hcast : (k.val:ℤ) = (j.val:ℤ) := hmod.trans hj.symm
      have hval : k.val = j.val := by exact_mod_cast hcast
      exact hkj (Fin.ext hval)
    have hsum :
        fourierCoeff ((∑ k : Fin M, circleCoverEmbedding T S M hM (k.val:ℤ)
            (circleCoverComponent T S M hM (k.val:ℤ) f)) : CircleL2 S) n =
          ∑ k : Fin M, fourierCoeff
            (circleCoverEmbedding T S M hM (k.val:ℤ)
              (circleCoverComponent T S M hM (k.val:ℤ) f)) n := by
      simp only [← fourierBasis_repr,HilbertBasis.repr_apply_apply,inner_sum]
    rw [hsum]
    symm
    rw [Finset.sum_eq_single j]
    · exact hmain
    · intro k _ hkj
      exact circle_cover_embedding_fourier_zero T S M hM (k.val:ℤ) n
        (circleCoverComponent T S M hM (k.val:ℤ) f) (hdisjoint k hkj)
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ j))
  have hinner : inner ℂ f f =
      ∑ j : Fin M, inner ℂ (circleCoverComponent T S M hM (j.val:ℤ) f)
        (circleCoverComponent T S M hM (j.val:ℤ) f) := by
    calc
      inner ℂ f f = inner ℂ
          (∑ j : Fin M, circleCoverEmbedding T S M hM (j.val:ℤ)
            (circleCoverComponent T S M hM (j.val:ℤ) f)) f :=
        congrArg (fun u : CircleL2 S => inner ℂ u f) hreconstruct
      _ = ∑ j : Fin M, inner ℂ
          (circleCoverEmbedding T S M hM (j.val:ℤ)
            (circleCoverComponent T S M hM (j.val:ℤ) f)) f := sum_inner _ _ _
      _ = _ := Finset.sum_congr rfl (fun j _ => circle_cover_embedding_inner T S M hM _ _ f)
  refine ⟨hreconstruct,?_⟩
  calc
    ‖f‖^2 = (inner ℂ f f).re := norm_sq_eq_re_inner (𝕜 := ℂ) f
    _ = (∑ j : Fin M, inner ℂ (circleCoverComponent T S M hM (j.val:ℤ) f)
        (circleCoverComponent T S M hM (j.val:ℤ) f)).re := congrArg Complex.re hinner
    _ = ∑ j : Fin M, (inner ℂ (circleCoverComponent T S M hM (j.val:ℤ) f)
        (circleCoverComponent T S M hM (j.val:ℤ) f)).re := map_sum Complex.reAddGroupHom _ _
    _ = ∑ j : Fin M, ‖circleCoverComponent T S M hM (j.val:ℤ) f‖^2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

end Lemniscate
