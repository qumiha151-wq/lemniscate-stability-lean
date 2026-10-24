import Lemniscate.OddSobolevSummability

/-! Dissipation on the infinite H2 coefficient domain. The proof passes to the
limit from arbitrary finite sets using the established absolute convergence. -/
namespace Lemniscate.OddArithmetic
open Finset Complex Filter
open scoped ComplexConjugate Topology

theorem odd_tendsto_finset_square :
    Tendsto (fun I : Finset ℤ => I.product I) atTop atTop := by
  apply Monotone.tendsto_atTop_atTop
  · intro I J h
    exact product_subset_product h h
  · intro E
    let I := E.image Prod.fst ∪ E.image Prod.snd
    refine ⟨I, ?_⟩
    intro p hp
    apply mem_product.mpr
    constructor
    · exact mem_union_left _ (mem_image.mpr ⟨p, hp, rfl⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨p, hp, rfl⟩)

theorem odd_energy_tendsto (v : ℤ → ℂ) (hv : HasOddH2Coefficients v)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    Tendsto (fun I : Finset ℤ => ∑ i ∈ I, ∑ j ∈ I, oddEnergyTerm α v (i,j))
      atTop (𝓝 (∑' p : ℤ × ℤ, oddEnergyTerm α v p)) := by
  have ht := (odd_energy_summable v hv α hα hα').hasSum.comp odd_tendsto_finset_square
  simpa only [Function.comp_def, Finset.product_eq_sprod, sum_product] using ht

noncomputable def oddH2Form (α : ℝ) (v : ℤ → ℂ) : ℝ :=
  (∑' p : ℤ × ℤ, oddEnergyTerm α v p).re

theorem odd_h2_form_of_finite_bound (v : ℤ → ℂ) (hv : HasOddH2Coefficients v)
    (α gap : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2)
    (hfinite : ∀ I : Finset ℤ,
      (∑ i ∈ I, ∑ j ∈ I, conj (v i)*(oddIndexedMatrix α i j:ℂ)*v j).re ≤
        -gap*(∑ i ∈ I, ‖v i‖^2)) :
    oddH2Form α v ≤ -gap*(∑' i : ℤ, ‖v i‖^2) := by
  have henergy : Tendsto
      (fun I : Finset ℤ => (∑ i ∈ I, ∑ j ∈ I, oddEnergyTerm α v (i,j)).re)
      atTop (𝓝 (oddH2Form α v)) :=
    (Complex.continuous_re.tendsto _).comp (odd_energy_tendsto v hv α hα hα')
  have hmass : Tendsto (fun I : Finset ℤ => ∑ i ∈ I, ‖v i‖^2)
      atTop (𝓝 (∑' i : ℤ, ‖v i‖^2)) := (odd_h2_coefficients_mass_summable v hv).hasSum
  apply le_of_tendsto_of_tendsto' henergy (hmass.const_mul (-gap))
  intro I
  exact hfinite I

theorem odd_h2_form_dissipative (v : ℤ → ℂ) (hv : HasOddH2Coefficients v)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    oddH2Form α v ≤ -(∑' i : ℤ, ‖v i‖^2) := by
  simpa only [neg_mul, one_mul] using odd_h2_form_of_finite_bound v hv α 1 hα hα'
    (fun I => by simpa only [neg_mul, one_mul] using odd_finite_form_dissipative I v α hα hα')

theorem odd_zero_h2_form_dissipative (v : ℤ → ℂ) (hv : HasOddH2Coefficients v) :
    oddH2Form 0 v ≤ -6*(∑' i : ℤ, ‖v i‖^2) :=
  odd_h2_form_of_finite_bound v hv 0 6 (by norm_num) (by norm_num)
    (fun I => odd_zero_finite_form_dissipative I v)

end Lemniscate.OddArithmetic
