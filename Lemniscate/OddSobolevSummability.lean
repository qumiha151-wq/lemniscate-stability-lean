import Lemniscate.OddSobolevKernel

/-! Absolute convergence of the complete odd energy on the H2 coefficient
domain at actual frequencies 2*i+1, uniformly on the parameter half interval. -/
namespace Lemniscate.OddArithmetic
open Finset Complex
open scoped ComplexConjugate

def HasOddH2Coefficients (v : ℤ → ℂ) : Prop :=
  Summable (fun i : ℤ => (oddFrequencyWeight i*‖v i‖)^2)

noncomputable def oddH2Mass (v : ℤ → ℂ) : ℝ :=
  ∑' i : ℤ, (oddFrequencyWeight i*‖v i‖)^2

noncomputable def absoluteOddTerm (α : ℝ) (v : ℤ → ℂ) (p : ℤ × ℤ) : ℝ :=
  |oddIndexedMatrix α p.1 p.2| * ‖v p.1‖*‖v p.2‖

noncomputable def oddEnergyTerm (α : ℝ) (v : ℤ → ℂ) (p : ℤ × ℤ) : ℂ :=
  conj (v p.1)*(oddIndexedMatrix α p.1 p.2:ℂ)*v p.2

theorem odd_finite_absolute_bound (I : Finset ℤ) (v : ℤ → ℂ) (α : ℝ)
    (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    (∑ i ∈ I, ∑ j ∈ I, |oddIndexedMatrix α i j| * ‖v i‖*‖v j‖) ≤
      512*(∑ i ∈ I, (oddFrequencyWeight i*‖v i‖)^2) := by
  have hs := weighted_double_sum_bound I
    (fun i j => oddSobolevKernel (i-j).natAbs) (fun _ => (1:ℝ))
    (fun i => oddFrequencyWeight i*‖v i‖) (fun _ _ => by norm_num)
    (fun i _ j _ => odd_sobolev_kernel_symmetric i j)
  have hs' :
      (∑ i ∈ I, ∑ j ∈ I, oddSobolevKernel (i-j).natAbs*(oddFrequencyWeight i*‖v i‖)*
        (oddFrequencyWeight j*‖v j‖)) ≤
      ∑ i ∈ I, (∑ j ∈ I, oddSobolevKernel (i-j).natAbs)*(oddFrequencyWeight i*‖v i‖)^2 := by
    simpa only [div_self (by norm_num : (1:ℝ) ≠ 0), mul_one,
      abs_of_nonneg (odd_sobolev_kernel_nonneg _)] using hs
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ I, oddSobolevKernel (i-j).natAbs*(oddFrequencyWeight i*‖v i‖)*
        (oddFrequencyWeight j*‖v j‖) := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      calc
        _ ≤ (oddSobolevKernel (i-j).natAbs*oddFrequencyWeight i*oddFrequencyWeight j)*‖v i‖*‖v j‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (odd_sobolev_entry_bound i j α hα hα') (norm_nonneg _))
            (norm_nonneg _)
        _ = _ := by ring
    _ ≤ _ := hs'
    _ ≤ _ := by
      rw [mul_sum]
      apply sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (odd_sobolev_kernel_finite_row_bound I i) (sq_nonneg _)

theorem odd_finite_pairs_absolute_bound (E : Finset (ℤ × ℤ)) (v : ℤ → ℂ)
    (hv : HasOddH2Coefficients v) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    (∑ p ∈ E, absoluteOddTerm α v p) ≤ 512*oddH2Mass v := by
  let I := E.image Prod.fst ∪ E.image Prod.snd
  have hsub : E ⊆ I.product I := by
    intro p hp
    apply mem_product.mpr
    constructor
    · exact mem_union_left _ (mem_image.mpr ⟨p, hp, rfl⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨p, hp, rfl⟩)
  calc
    _ ≤ ∑ p ∈ I.product I, absoluteOddTerm α v p :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by unfold absoluteOddTerm; positivity)
    _ = ∑ i ∈ I, ∑ j ∈ I, |oddIndexedMatrix α i j| * ‖v i‖*‖v j‖ := by
      simpa only [Finset.product_eq_sprod, absoluteOddTerm] using
        (Finset.sum_product I I (absoluteOddTerm α v))
    _ ≤ 512*(∑ i ∈ I, (oddFrequencyWeight i*‖v i‖)^2) := odd_finite_absolute_bound I v α hα hα'
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Summable.sum_le_tsum I (fun i _ => sq_nonneg _) hv) (by norm_num)

theorem odd_absolute_summable (v : ℤ → ℂ) (hv : HasOddH2Coefficients v)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) : Summable (absoluteOddTerm α v) := by
  exact summable_of_sum_le (fun p => by unfold absoluteOddTerm; positivity)
    (fun E => odd_finite_pairs_absolute_bound E v hv α hα hα')

theorem odd_energy_term_norm (α : ℝ) (v : ℤ → ℂ) (p : ℤ × ℤ) :
    ‖oddEnergyTerm α v p‖ = absoluteOddTerm α v p := by
  simp only [oddEnergyTerm, absoluteOddTerm, norm_mul, norm_conj,
    Complex.norm_real, Real.norm_eq_abs]
  ring

theorem odd_energy_summable (v : ℤ → ℂ) (hv : HasOddH2Coefficients v)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) : Summable (oddEnergyTerm α v) := by
  apply Summable.of_norm
  simpa only [odd_energy_term_norm] using odd_absolute_summable v hv α hα hα'

theorem odd_absolute_tsum_bound (v : ℤ → ℂ) (hv : HasOddH2Coefficients v)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    (∑' p : ℤ × ℤ, absoluteOddTerm α v p) ≤ 512*oddH2Mass v :=
  Real.tsum_le_of_sum_le (fun p => by unfold absoluteOddTerm; positivity)
    (fun E => odd_finite_pairs_absolute_bound E v hv α hα hα')

theorem odd_h2_coefficients_mass_summable (v : ℤ → ℂ) (hv : HasOddH2Coefficients v) :
    Summable (fun i : ℤ => ‖v i‖^2) := by
  apply Summable.of_nonneg_of_le (fun i => sq_nonneg _) _ hv
  intro i
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (odd_frequency_weight_one_le i) (norm_nonneg (v i))

end Lemniscate.OddArithmetic
