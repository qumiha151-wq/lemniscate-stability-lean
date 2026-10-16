import Lemniscate.SobolevDissipation
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! The normalized even cosine family obtained from a two-sided orthonormal
Fourier family. Its synthesis map is an actual Hilbert-space isometry. -/
namespace Lemniscate
open Complex
open scoped ComplexConjugate

noncomputable def evenCosineFactor : ℂ := ((1/Real.sqrt 2 : ℝ):ℂ)

theorem evenCosineFactor_conj : conj evenCosineFactor = evenCosineFactor := by
  simp [evenCosineFactor]

theorem evenCosineFactor_normalization :
    evenCosineFactor*(evenCosineFactor*2) = 1 := by
  have hs : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (2:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have h : (1/Real.sqrt (2:ℝ))*(1/Real.sqrt 2*2) = 1 := by
    field_simp [hn]
    nlinarith
  unfold evenCosineFactor
  exact_mod_cast h

noncomputable def evenCosineMode {E : Type*} [AddCommGroup E] [Module ℂ E]
    (b : ℤ → E) (j : ℕ) : E :=
  if j = 0 then b 0 else evenCosineFactor • (b (2*(j:ℤ))+b (-(2*(j:ℤ))))

section Inner
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem even_cosine_orthonormal (b : ℤ → E) (hb : Orthonormal ℂ b) :
    Orthonormal ℂ (evenCosineMode b) := by
  apply orthonormal_iff_ite.mpr
  intro j k
  have hg := orthonormal_iff_ite.mp hb
  by_cases hj : j = 0
  · subst j
    by_cases hk : k = 0
    · subst k
      simpa only [evenCosineMode, if_pos rfl, ite_true] using hg 0 0
    · have hp : (0:ℤ) ≠ 2*(k:ℤ) := by omega
      have hn : (0:ℤ) ≠ -(2*(k:ℤ)) := by omega
      simp [evenCosineMode, hk, Ne.symm hk, inner_smul_right, inner_add_right, hg, hp, hn]
  · by_cases hk : k = 0
    · subst k
      have hp : 2*(j:ℤ) ≠ (0:ℤ) := by omega
      have hn : -(2*(j:ℤ)) ≠ (0:ℤ) := by omega
      simp [evenCosineMode, hj, inner_smul_left, inner_add_left, hg, hp, hn]
    · by_cases he : j = k
      · subst k
        have hpn : 2*(j:ℤ) ≠ -(2*(j:ℤ)) := by omega
        have hsum : inner ℂ (b (2*(j:ℤ))+b (-(2*(j:ℤ))))
            (b (2*(j:ℤ))+b (-(2*(j:ℤ)))) = 2 := by
          simp only [inner_add_left, inner_add_right, hg]
          norm_num [hpn, Ne.symm hpn]
        simp only [evenCosineMode, if_neg hj, ite_true,
          inner_smul_left, inner_smul_right, hsum, evenCosineFactor_conj]
        exact evenCosineFactor_normalization
      · have hpp : 2*(j:ℤ) ≠ 2*(k:ℤ) := by omega
        have hpn : 2*(j:ℤ) ≠ -(2*(k:ℤ)) := by omega
        have hnp : -(2*(j:ℤ)) ≠ 2*(k:ℤ) := by omega
        have hnn : -(2*(j:ℤ)) ≠ -(2*(k:ℤ)) := by omega
        have hsum : inner ℂ (b (2*(j:ℤ))+b (-(2*(j:ℤ))))
            (b (2*(k:ℤ))+b (-(2*(k:ℤ)))) = 0 := by
          simp [inner_add_left, inner_add_right, hg, hpp, hpn, hnp, hnn]
        simp only [evenCosineMode, if_neg hj, if_neg hk, if_neg he,
          inner_smul_left, inner_smul_right, hsum, mul_zero]

noncomputable abbrev CosineSequenceSpace := lp (fun _ : ℕ => ℂ) 2

variable [CompleteSpace E]

noncomputable def evenCosineSynthesis (b : ℤ → E) (hb : Orthonormal ℂ b) :
    CosineSequenceSpace →ₗᵢ[ℂ] E :=
  (even_cosine_orthonormal b hb).orthogonalFamily.linearIsometry

theorem even_cosine_synthesis_norm (b : ℤ → E) (hb : Orthonormal ℂ b)
    (v : CosineSequenceSpace) : ‖evenCosineSynthesis b hb v‖ = ‖v‖ :=
  (evenCosineSynthesis b hb).norm_map v

theorem even_cosine_hasSum (b : ℤ → E) (hb : Orthonormal ℂ b)
    (v : CosineSequenceSpace) :
    HasSum (fun j : ℕ => v j • evenCosineMode b j) (evenCosineSynthesis b hb v) := by
  simpa only [evenCosineSynthesis, LinearIsometry.toSpanSingleton_apply] using
    (even_cosine_orthonormal b hb).orthogonalFamily.hasSum_linearIsometry v

end Inner
end Lemniscate
