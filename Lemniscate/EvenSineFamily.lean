import Lemniscate.EvenCosineFamily

/-! The normalized sine family from a two-sided complex orthonormal Fourier
family. Index j represents positive frequency 2(j+1), with no zero sine mode. -/
namespace Lemniscate
open Complex
open scoped ComplexConjugate

noncomputable def evenSineFactor : ℂ := -I*evenCosineFactor

theorem evenSineFactor_conj : conj evenSineFactor = -evenSineFactor := by
  simp [evenSineFactor, evenCosineFactor_conj]

theorem evenSineFactor_normalization :
    conj evenSineFactor*(evenSineFactor*2) = 1 := by
  calc
    _ = -I^2*(evenCosineFactor*(evenCosineFactor*2)) := by
      simp only [evenSineFactor, map_mul, map_neg, Complex.conj_I,
        evenCosineFactor_conj, neg_neg]
      ring
    _ = 1 := by rw [Complex.I_sq, evenCosineFactor_normalization]; norm_num

theorem evenSineFactor_ne_zero : evenSineFactor ≠ 0 := by
  intro h
  have hn := evenSineFactor_normalization
  rw [h] at hn
  norm_num at hn

noncomputable def evenSineMode {E : Type*} [AddCommGroup E] [Module ℂ E]
    (b : ℤ → E) (j : ℕ) : E :=
  evenSineFactor • (b (2*((j+1:ℕ):ℤ))-b (-(2*((j+1:ℕ):ℤ))))

section Inner
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem even_sine_orthonormal (b : ℤ → E) (hb : Orthonormal ℂ b) :
    Orthonormal ℂ (evenSineMode b) := by
  apply orthonormal_iff_ite.mpr
  intro j k
  have hg := orthonormal_iff_ite.mp hb
  by_cases he : j = k
  · subst k
    have hpn : 2*((j+1:ℕ):ℤ) ≠ -(2*((j+1:ℕ):ℤ)) := by omega
    have hs : inner ℂ (b (2*((j+1:ℕ):ℤ))-b (-(2*((j+1:ℕ):ℤ))))
        (b (2*((j+1:ℕ):ℤ))-b (-(2*((j+1:ℕ):ℤ)))) = 2 := by
      simp only [inner_sub_left, inner_sub_right, hg]
      simp only [hpn, Ne.symm hpn, if_false, if_true]
      norm_num
    simp only [evenSineMode, ite_true, inner_smul_left, inner_smul_right, hs]
    calc
      _ = conj evenSineFactor*(evenSineFactor*2) := by ring
      _ = 1 := evenSineFactor_normalization
  · have hpp : 2*((j+1:ℕ):ℤ) ≠ 2*((k+1:ℕ):ℤ) := by omega
    have hpn : 2*((j+1:ℕ):ℤ) ≠ -(2*((k+1:ℕ):ℤ)) := by omega
    have hnp : -(2*((j+1:ℕ):ℤ)) ≠ 2*((k+1:ℕ):ℤ) := by omega
    have hnn : -(2*((j+1:ℕ):ℤ)) ≠ -(2*((k+1:ℕ):ℤ)) := by omega
    simp only [evenSineMode, he, if_false, inner_smul_left, inner_smul_right,
      inner_sub_left, inner_sub_right, hg, hpp, hpn, hnp, hnn, if_false]
    ring

noncomputable abbrev SineSequenceSpace := lp (fun _ : ℕ => ℂ) 2

variable [CompleteSpace E]

noncomputable def evenSineSynthesis (b : ℤ → E) (hb : Orthonormal ℂ b) :
    SineSequenceSpace →ₗᵢ[ℂ] E :=
  (even_sine_orthonormal b hb).orthogonalFamily.linearIsometry

theorem even_sine_synthesis_norm (b : ℤ → E) (hb : Orthonormal ℂ b)
    (v : SineSequenceSpace) : ‖evenSineSynthesis b hb v‖ = ‖v‖ :=
  (evenSineSynthesis b hb).norm_map v

theorem even_sine_hasSum (b : ℤ → E) (hb : Orthonormal ℂ b) (v : SineSequenceSpace) :
    HasSum (fun j : ℕ => v j • evenSineMode b j) (evenSineSynthesis b hb v) := by
  simpa only [evenSineSynthesis, LinearIsometry.toSpanSingleton_apply] using
    (even_sine_orthonormal b hb).orthogonalFamily.hasSum_linearIsometry v

end Inner
end Lemniscate
