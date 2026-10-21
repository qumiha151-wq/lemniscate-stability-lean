import Lemniscate.SineTailSummability

/-! The bound -100 for the full sine tail-block form on H2-weighted complex
sequences. Absolute convergence and passage from finite sums are proved. -/
namespace Lemniscate.CoarseArithmetic
open Finset Complex Filter
open scoped Topology

noncomputable def sineTailH2Form (v : ℕ → ℂ) : ℝ :=
  (∑' p : ℕ × ℕ, sineTailEnergyTerm v p).re

theorem sine_tail_energy_tendsto (v : ℕ → ℂ) (hv : HasSineTailH2Coefficients v) :
    Tendsto (fun I : Finset ℕ => ∑ i ∈ I, ∑ j ∈ I, sineTailEnergyTerm v (i,j))
      atTop (𝓝 (∑' p : ℕ × ℕ, sineTailEnergyTerm v p)) := by
  have h := (sine_tail_energy_summable v hv).hasSum.comp tendsto_finset_square
  simpa only [Function.comp_def, Finset.product_eq_sprod, sum_product] using h

theorem sine_tail_h2_form_dissipative (v : ℕ → ℂ) (hv : HasSineTailH2Coefficients v) :
    sineTailH2Form v ≤ -100*(∑' j : ℕ, ‖v j‖^2) := by
  have henergy : Tendsto
      (fun I : Finset ℕ => (∑ i ∈ I, ∑ j ∈ I, sineTailEnergyTerm v (i,j)).re)
      atTop (𝓝 (sineTailH2Form v)) :=
    (Complex.continuous_re.tendsto _).comp (sine_tail_energy_tendsto v hv)
  have hmass : Tendsto (fun I : Finset ℕ => ∑ j ∈ I, ‖v j‖^2)
      atTop (𝓝 (∑' j : ℕ, ‖v j‖^2)) :=
    (h2_coefficients_mass_summable v ((sine_tail_h2_iff v).mp hv)).hasSum
  apply le_of_tendsto_of_tendsto' henergy (hmass.const_mul (-100))
  intro I
  simpa only [sineTailEnergyTerm] using sine_tail_finite_form_dissipative I v

end Lemniscate.CoarseArithmetic
