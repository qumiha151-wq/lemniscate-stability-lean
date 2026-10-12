import Lemniscate.WeightedRows
import Mathlib.Analysis.Complex.Basic

/-! Weighted rows for complex Fourier coefficients. Symmetry is imposed on
entry norms, which in particular holds for every Hermitian matrix. -/
namespace Lemniscate
open Finset Complex
open scoped ComplexConjugate

theorem complex_double_sum_majorant {ι : Type*} (I : Finset ι)
    (A : ι → ι → ℂ) (v : ι → ℂ) :
    (∑ i ∈ I, ∑ j ∈ I, conj (v i)*A i j*v j).re ≤
      ∑ i ∈ I, ∑ j ∈ I, ‖A i j‖*‖v i‖*‖v j‖ := by
  change Complex.reCLM (∑ i ∈ I, ∑ j ∈ I, conj (v i)*A i j*v j) ≤ _
  simp only [map_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  calc
    _ ≤ ‖conj (v i)*A i j*v j‖ := Complex.re_le_norm _
    _ = _ := by simp only [norm_mul, norm_conj]; ring

theorem complex_weighted_row_dissipation {ι : Type*} (I : Finset ι)
    (diagonal : ι → ℝ) (off : ι → ι → ℂ) (d : ι → ℝ) (v : ι → ℂ) (gap : ℝ)
    (hd : ∀ i ∈ I, 0 < d i)
    (hsym : ∀ i ∈ I, ∀ j ∈ I, ‖off i j‖ = ‖off j i‖)
    (hrow : ∀ i ∈ I, diagonal i+∑ j ∈ I, ‖off i j‖*(d j/d i) ≤ -gap) :
    (∑ i ∈ I, diagonal i*‖v i‖^2) +
      (∑ i ∈ I, ∑ j ∈ I, conj (v i)*off i j*v j).re ≤
        -gap*(∑ i ∈ I, ‖v i‖^2) := by
  have h := weighted_row_dissipation I diagonal (fun i j => ‖off i j‖)
    d (fun i => ‖v i‖) gap hd hsym (by simpa only [abs_norm] using hrow)
  have hm := complex_double_sum_majorant I off v
  linarith

theorem hermitian_entry_norm_symmetry {ι : Type*} (A : ι → ι → ℂ)
    (h : ∀ i j, A j i = conj (A i j)) (i j : ι) : ‖A i j‖ = ‖A j i‖ := by
  rw [h i j, norm_conj]

end Lemniscate
