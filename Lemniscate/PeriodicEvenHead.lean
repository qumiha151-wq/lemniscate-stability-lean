import Lemniscate.PeriodicBlochFourier

/-! Orthogonal decomposition into the 31 ordinary even Fourier modes
of absolute frequency below 32 and their complement. Development source. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

def evenHeadFrequency (j : Fin 31) : ℤ := 2*(j.val:ℤ)-30

theorem even_head_frequency_injective : Function.Injective evenHeadFrequency := by
  intro i j hij
  apply Fin.ext
  dsimp only [evenHeadFrequency] at hij
  omega

theorem even_head_frequency_range (n : ℤ) :
    (∃ j : Fin 31, evenHeadFrequency j = n) ↔ Even n ∧ |(n:ℝ)| < 32 := by
  constructor
  · rintro ⟨j, rfl⟩
    constructor
    · exact ⟨(j.val:ℤ)-15, by dsimp [evenHeadFrequency]; ring⟩
    · have hj := j.isLt
      have hlo : (-32:ℤ) < 2*(j.val:ℤ)-30 := by omega
      have hhi : 2*(j.val:ℤ)-30 < 32 := by omega
      rw [abs_lt]
      constructor
      · exact_mod_cast hlo
      · exact_mod_cast hhi
  · rintro ⟨⟨k, hk⟩, hn⟩
    have hn' : -32 < n ∧ n < 32 := by exact_mod_cast (abs_lt.mp hn)
    have hk0 : 0 ≤ k+15 := by omega
    have hk31 : (k+15).toNat < 31 := by omega
    refine ⟨⟨(k+15).toNat, hk31⟩, ?_⟩
    simp only [evenHeadFrequency, Int.toNat_of_nonneg hk0]
    omega

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleEvenHeadH4 (v : Fin 31 → ℂ) : circleH4Domain T :=
  ∑ j, v j • circleFourierH4 T (evenHeadFrequency j)

theorem circle_even_head_h4_coe (v : Fin 31 → ℂ) :
    (circleEvenHeadH4 T v : CircleL2 T) =
      ∑ j, v j • fourierBasis (T := T) (evenHeadFrequency j) := by
  simp only [circleEvenHeadH4, Submodule.coe_sum, Submodule.coe_smul_of_tower,
    circleFourierH4]

theorem circle_even_head_fourier (v : Fin 31 → ℂ) (n : ℤ) :
    fourierCoeff (circleEvenHeadH4 T v : CircleL2 T) n =
      ∑ j, v j*(if n = evenHeadFrequency j then 1 else 0) := by
  rw [← fourierBasis_repr, HilbertBasis.repr_apply_apply, circle_even_head_h4_coe]
  simp only [inner_sum, inner_smul_right,
    orthonormal_iff_ite.mp (fourierBasis (T := T)).orthonormal]

theorem circle_even_head_fourier_at (v : Fin 31 → ℂ) (j : Fin 31) :
    fourierCoeff (circleEvenHeadH4 T v : CircleL2 T) (evenHeadFrequency j) = v j := by
  rw [circle_even_head_fourier]
  simp only [even_head_frequency_injective.eq_iff, mul_ite, mul_one, mul_zero]
  simp

theorem circle_even_head_fourier_outside (v : Fin 31 → ℂ) (n : ℤ)
    (hn : ∀ j, n ≠ evenHeadFrequency j) :
    fourierCoeff (circleEvenHeadH4 T v : CircleL2 T) n = 0 := by
  rw [circle_even_head_fourier]
  simp only [if_neg (hn _), mul_zero, Finset.sum_const_zero]

theorem circle_even_head_norm_sq (v : Fin 31 → ℂ) :
    ‖(circleEvenHeadH4 T v : CircleL2 T)‖^2 = ∑ j, ‖v j‖^2 := by
  have hon := (fourierBasis (T := T)).orthonormal.comp evenHeadFrequency
    even_head_frequency_injective
  have h := hon.inner_sum v v Finset.univ
  simp only [Function.comp_apply] at h
  rw [circle_even_head_h4_coe, norm_sq_eq_re_inner (𝕜 := ℂ)]
  change (inner ℂ (∑ j, v j • fourierBasis (T := T) (evenHeadFrequency j))
    (∑ j, v j • fourierBasis (T := T) (evenHeadFrequency j))).re = _
  rw [h]
  change Complex.reCLM (∑ j, conj (v j)*v j) = _
  simp only [map_sum]
  change (∑ j, (conj (v j)*v j).re) = _
  simp only [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.sq_norm]

theorem circle_even_head_operator_pairing (A : circleH4Domain T →ₗ[ℂ] CircleL2 T)
    (v w : Fin 31 → ℂ) :
    inner ℂ (circleEvenHeadH4 T v : CircleL2 T) (A (circleEvenHeadH4 T w)) =
      ∑ i, ∑ j, conj (v i)*
        inner ℂ (fourierBasis (T := T) (evenHeadFrequency i))
          (A (circleFourierH4 T (evenHeadFrequency j)))*w j := by
  rw [circle_even_head_h4_coe]
  simp only [circleEvenHeadH4, map_sum, map_smul, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

noncomputable def circleEvenHeadProjection (f : circleH4Domain T) : circleH4Domain T :=
  circleEvenHeadH4 T (fun j => fourierCoeff (f : CircleL2 T) (evenHeadFrequency j))

theorem circle_even_head_remainder_high (f : circleH4Domain T)
    (hf : ∀ n : ℤ, Odd n → fourierCoeff (f : CircleL2 T) n = 0)
    (n : ℤ) (hn : |(n:ℝ)| < 32) :
    fourierCoeff ((f-circleEvenHeadProjection T f : circleH4Domain T) : CircleL2 T) n = 0 := by
  change fourierCoeff ((f : CircleL2 T)-(circleEvenHeadProjection T f : CircleL2 T)) n = 0
  rw [circle_fourierCoeff_sub]
  rcases Int.even_or_odd n with he | ho
  · obtain ⟨j, rfl⟩ := (even_head_frequency_range n).mpr ⟨he, hn⟩
    rw [circleEvenHeadProjection, circle_even_head_fourier_at, sub_self]
  · rw [hf n ho, circleEvenHeadProjection, circle_even_head_fourier_outside]
    · exact sub_self 0
    · intro j hj
      have he := ((even_head_frequency_range n).mp ⟨j, hj.symm⟩).1
      exact (Int.not_even_iff_odd.mpr ho) he

theorem circle_even_head_remainder_orthogonal (f : circleH4Domain T) :
    inner ℂ (circleEvenHeadProjection T f : CircleL2 T)
      ((f-circleEvenHeadProjection T f : circleH4Domain T) : CircleL2 T) = 0 := by
  have hb (j : Fin 31) :
      inner ℂ (fourierBasis (T := T) (evenHeadFrequency j))
        ((f-circleEvenHeadProjection T f : circleH4Domain T) : CircleL2 T) = 0 := by
    rw [← HilbertBasis.repr_apply_apply, fourierBasis_repr]
    change fourierCoeff ((f : CircleL2 T)-(circleEvenHeadProjection T f : CircleL2 T)) _ = 0
    rw [circle_fourierCoeff_sub, circleEvenHeadProjection, circle_even_head_fourier_at, sub_self]
  change inner ℂ (circleEvenHeadH4 T
    (fun j => fourierCoeff (f : CircleL2 T) (evenHeadFrequency j)) : CircleL2 T)
      ((f-circleEvenHeadProjection T f : circleH4Domain T) : CircleL2 T) = 0
  rw [circle_even_head_h4_coe]
  simp only [sum_inner, inner_smul_left, hb, mul_zero, Finset.sum_const_zero]

theorem circle_even_head_norm_decomposition (f : circleH4Domain T) :
    ‖(f : CircleL2 T)‖^2 = ‖(circleEvenHeadProjection T f : CircleL2 T)‖^2+
      ‖((f-circleEvenHeadProjection T f : circleH4Domain T) : CircleL2 T)‖^2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (circleEvenHeadProjection T f : CircleL2 T)
    ((f-circleEvenHeadProjection T f : circleH4Domain T) : CircleL2 T)
    (circle_even_head_remainder_orthogonal T f)
  have heq : (circleEvenHeadProjection T f : CircleL2 T)+
      ((f-circleEvenHeadProjection T f : circleH4Domain T) : CircleL2 T) = (f : CircleL2 T) := by
    change _+((f : CircleL2 T)-_) = _
    abel
  rw [heq] at h
  simpa only [pow_two] using h

end Lemniscate
