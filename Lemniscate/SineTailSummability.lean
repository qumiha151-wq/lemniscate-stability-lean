import Lemniscate.SineSobolevEntries

/-! Absolute convergence of the complete sine tail-block energy on H2
coefficient sequences. The frequency represented by index j is 2(j+2). -/
namespace Lemniscate.CoarseArithmetic
open Finset Complex
open scoped ComplexConjugate

noncomputable def sineTailH2Mass (v : ℕ → ℂ) : ℝ :=
  ∑' j : ℕ, (frequencyWeight (j+2)*‖v j‖)^2

noncomputable def absoluteSineTailTerm (v : ℕ → ℂ) (p : ℕ × ℕ) : ℝ :=
  |sineMatrixEntry thetaParameter nome (p.1+2) (p.2+2)| * ‖v p.1‖*‖v p.2‖

noncomputable def sineTailEnergyTerm (v : ℕ → ℂ) (p : ℕ × ℕ) : ℂ :=
  conj (v p.1)*(sineMatrixEntry thetaParameter nome (p.1+2) (p.2+2):ℂ)*v p.2

theorem sine_tail_finite_absolute_bound (I : Finset ℕ) (v : ℕ → ℂ) :
    (∑ i ∈ I, ∑ j ∈ I, |sineMatrixEntry thetaParameter nome (i+2) (j+2)| * ‖v i‖*‖v j‖) ≤
      1024*(∑ i ∈ I, (frequencyWeight (i+2)*‖v i‖)^2) := by
  have hs := weighted_double_sum_bound I
    (fun i j => cosineKernel (i-j+(j-i))) (fun _ => (1:ℝ))
    (fun i => frequencyWeight (i+2)*‖v i‖) (fun _ _ => by norm_num)
    (fun i _ j _ => by congr 1; omega)
  have hs' :
      (∑ i ∈ I, ∑ j ∈ I, cosineKernel (i-j+(j-i))*(frequencyWeight (i+2)*‖v i‖)*
        (frequencyWeight (j+2)*‖v j‖)) ≤
      ∑ i ∈ I, (∑ j ∈ I, cosineKernel (i-j+(j-i)))*(frequencyWeight (i+2)*‖v i‖)^2 := by
    simpa only [div_self (by norm_num : (1:ℝ) ≠ 0), mul_one,
      abs_of_nonneg (cosineKernel_nonneg _)] using hs
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ I, cosineKernel (i-j+(j-i))*(frequencyWeight (i+2)*‖v i‖)*
        (frequencyWeight (j+2)*‖v j‖) := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      calc
        _ ≤ (cosineKernel (i-j+(j-i))*frequencyWeight (i+2)*frequencyWeight (j+2))*
            ‖v i‖*‖v j‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (sine_tail_sobolev_entry_bound i j) (norm_nonneg _))
            (norm_nonneg _)
        _ = _ := by ring
    _ ≤ _ := hs'
    _ ≤ _ := by
      rw [mul_sum]
      apply sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (cosine_kernel_finite_row_bound I i) (sq_nonneg _)

theorem sine_tail_finite_pairs_absolute_bound (E : Finset (ℕ × ℕ)) (v : ℕ → ℂ)
    (hv : HasSineTailH2Coefficients v) :
    (∑ p ∈ E, absoluteSineTailTerm v p) ≤ 1024*sineTailH2Mass v := by
  let I := E.image Prod.fst ∪ E.image Prod.snd
  have hsub : E ⊆ I.product I := by
    intro p hp
    apply mem_product.mpr
    constructor
    · exact mem_union_left _ (mem_image.mpr ⟨p, hp, rfl⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨p, hp, rfl⟩)
  calc
    _ ≤ ∑ p ∈ I.product I, absoluteSineTailTerm v p :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by unfold absoluteSineTailTerm; positivity)
    _ = ∑ i ∈ I, ∑ j ∈ I,
        |sineMatrixEntry thetaParameter nome (i+2) (j+2)| * ‖v i‖*‖v j‖ := by
      simpa only [Finset.product_eq_sprod, absoluteSineTailTerm] using
        (Finset.sum_product I I (absoluteSineTailTerm v))
    _ ≤ 1024*(∑ i ∈ I, (frequencyWeight (i+2)*‖v i‖)^2) := sine_tail_finite_absolute_bound I v
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Summable.sum_le_tsum I (fun i _ => sq_nonneg _) hv) (by norm_num)

theorem sine_tail_absolute_summable (v : ℕ → ℂ) (hv : HasSineTailH2Coefficients v) :
    Summable (absoluteSineTailTerm v) :=
  summable_of_sum_le (fun p => by unfold absoluteSineTailTerm; positivity)
    (fun E => sine_tail_finite_pairs_absolute_bound E v hv)

theorem sine_tail_energy_term_norm (v : ℕ → ℂ) (p : ℕ × ℕ) :
    ‖sineTailEnergyTerm v p‖ = absoluteSineTailTerm v p := by
  simp only [sineTailEnergyTerm, absoluteSineTailTerm, norm_mul, norm_conj,
    Complex.norm_real, Real.norm_eq_abs]
  ring

theorem sine_tail_energy_summable (v : ℕ → ℂ) (hv : HasSineTailH2Coefficients v) :
    Summable (sineTailEnergyTerm v) := by
  apply Summable.of_norm
  simpa only [sine_tail_energy_term_norm] using sine_tail_absolute_summable v hv

end Lemniscate.CoarseArithmetic
