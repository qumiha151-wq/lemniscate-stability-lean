import Lemniscate.SobolevKernel

/-! Absolute convergence of the concrete cosine energy for H2-weighted complex
sequences. Identification of this coefficient space with periodic Sobolev
functions is a separate Fourier-analysis obligation. -/
namespace Lemniscate.CoarseArithmetic
open Finset Complex
open scoped ComplexConjugate

def HasH2Coefficients (v : ℕ → ℂ) : Prop :=
  Summable (fun j : ℕ => (frequencyWeight j*‖v j‖)^2)

noncomputable def h2Mass (v : ℕ → ℂ) : ℝ :=
  ∑' j : ℕ, (frequencyWeight j*‖v j‖)^2

noncomputable def absoluteCosineTerm (v : ℕ → ℂ) (p : ℕ × ℕ) : ℝ :=
  |cosineMatrixEntry thetaParameter nome p.1 p.2| * ‖v p.1‖*‖v p.2‖

noncomputable def cosineEnergyTerm (v : ℕ → ℂ) (p : ℕ × ℕ) : ℂ :=
  conj (v p.1)*(cosineMatrixEntry thetaParameter nome p.1 p.2:ℂ)*v p.2

theorem cosine_finite_absolute_bound (I : Finset ℕ) (v : ℕ → ℂ) :
    (∑ i ∈ I, ∑ j ∈ I, |cosineMatrixEntry thetaParameter nome i j| * ‖v i‖*‖v j‖) ≤
      1024*(∑ i ∈ I, (frequencyWeight i*‖v i‖)^2) := by
  have hs := weighted_double_sum_bound I
    (fun i j => cosineKernel (i-j+(j-i))) (fun _ => (1:ℝ))
    (fun i => frequencyWeight i*‖v i‖) (fun _ _ => by norm_num)
    (fun i _ j _ => by congr 1; omega)
  have hs' :
      (∑ i ∈ I, ∑ j ∈ I, cosineKernel (i-j+(j-i))*(frequencyWeight i*‖v i‖)*
        (frequencyWeight j*‖v j‖)) ≤
      ∑ i ∈ I, (∑ j ∈ I, cosineKernel (i-j+(j-i)))*(frequencyWeight i*‖v i‖)^2 := by
    simpa only [div_self (by norm_num : (1:ℝ) ≠ 0), mul_one,
      abs_of_nonneg (cosineKernel_nonneg _)] using hs
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ I, cosineKernel (i-j+(j-i))*(frequencyWeight i*‖v i‖)*
        (frequencyWeight j*‖v j‖) := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      calc
        _ ≤ (cosineKernel (i-j+(j-i))*frequencyWeight i*frequencyWeight j)*‖v i‖*‖v j‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (cosine_sobolev_entry_bound i j) (norm_nonneg _))
            (norm_nonneg _)
        _ = _ := by ring
    _ ≤ _ := hs'
    _ ≤ _ := by
      rw [mul_sum]
      apply sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (cosine_kernel_finite_row_bound I i) (sq_nonneg _)

theorem cosine_finite_pairs_absolute_bound (E : Finset (ℕ × ℕ)) (v : ℕ → ℂ)
    (hv : HasH2Coefficients v) :
    (∑ p ∈ E, absoluteCosineTerm v p) ≤ 1024*h2Mass v := by
  let I := E.image Prod.fst ∪ E.image Prod.snd
  have hsub : E ⊆ I.product I := by
    intro p hp
    apply mem_product.mpr
    constructor
    · exact mem_union_left _ (mem_image.mpr ⟨p, hp, rfl⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨p, hp, rfl⟩)
  calc
    _ ≤ ∑ p ∈ I.product I, absoluteCosineTerm v p :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by unfold absoluteCosineTerm; positivity)
    _ = ∑ i ∈ I, ∑ j ∈ I, |cosineMatrixEntry thetaParameter nome i j| * ‖v i‖*‖v j‖ := by
      simpa only [Finset.product_eq_sprod, absoluteCosineTerm] using
        (Finset.sum_product I I (absoluteCosineTerm v))
    _ ≤ 1024*(∑ i ∈ I, (frequencyWeight i*‖v i‖)^2) := cosine_finite_absolute_bound I v
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Summable.sum_le_tsum I (fun i _ => sq_nonneg _) hv) (by norm_num)

theorem cosine_absolute_summable (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    Summable (absoluteCosineTerm v) := by
  exact summable_of_sum_le (fun p => by unfold absoluteCosineTerm; positivity)
    (fun E => cosine_finite_pairs_absolute_bound E v hv)

theorem cosine_energy_term_norm (v : ℕ → ℂ) (p : ℕ × ℕ) :
    ‖cosineEnergyTerm v p‖ = absoluteCosineTerm v p := by
  simp only [cosineEnergyTerm, absoluteCosineTerm, norm_mul, norm_conj,
    Complex.norm_real, Real.norm_eq_abs]
  ring

theorem cosine_energy_summable (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    Summable (cosineEnergyTerm v) := by
  apply Summable.of_norm
  simpa only [cosine_energy_term_norm] using cosine_absolute_summable v hv

theorem cosine_absolute_tsum_bound (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    (∑' p : ℕ × ℕ, absoluteCosineTerm v p) ≤ 1024*h2Mass v :=
  Real.tsum_le_of_sum_le (fun p => by unfold absoluteCosineTerm; positivity)
    (fun E => cosine_finite_pairs_absolute_bound E v hv)

end Lemniscate.CoarseArithmetic
