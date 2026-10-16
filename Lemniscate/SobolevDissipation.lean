import Lemniscate.SobolevSummability

/-! Passing the finite-mode dissipation estimate to all H2-weighted complex
sequences. Absolute convergence is proved in SobolevSummability, not assumed
as a new analytic hypothesis. The Sobolev-function Fourier identification is
still separate. -/
namespace Lemniscate.CoarseArithmetic
open Finset Complex Filter
open scoped ComplexConjugate Topology

/-- The sequence condition is equivalent to the weight at the actual
Fourier frequency 2j, rather than merely the index j. -/
theorem h2_coefficients_iff_even_frequency (v : ℕ → ℂ) :
    HasH2Coefficients v ↔
      Summable (fun j : ℕ => ((1+(2*(j:ℝ))^2)*‖v j‖)^2) := by
  constructor
  · intro hv
    apply Summable.of_nonneg_of_le (fun j => sq_nonneg _) _ (hv.mul_left 16)
    intro j
    have hw : 1+(2*(j:ℝ))^2 ≤ 4*frequencyWeight j := by
      unfold frequencyWeight
      nlinarith [sq_nonneg (j:ℝ)]
    have hm := mul_le_mul_of_nonneg_right hw (norm_nonneg (v j))
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (1+(2*(j:ℝ))^2)*‖v j‖) hm 2
    convert! hp using 1 <;> ring
  · intro hv
    apply Summable.of_nonneg_of_le (fun j => sq_nonneg _) _ hv
    intro j
    have hw : frequencyWeight j ≤ 1+(2*(j:ℝ))^2 := by
      unfold frequencyWeight
      nlinarith [sq_nonneg (j:ℝ)]
    exact pow_le_pow_left₀
      (mul_nonneg (frequencyWeight_pos j).le (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hw (norm_nonneg _)) 2

theorem h2_coefficients_mass_summable (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    Summable (fun j : ℕ => ‖v j‖^2) := by
  apply Summable.of_nonneg_of_le (fun j => sq_nonneg _) _ hv
  intro j
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  have hw : (1:ℝ) ≤ frequencyWeight j := by
    unfold frequencyWeight
    linarith [sq_nonneg (j:ℝ)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (norm_nonneg (v j))

theorem tendsto_finset_square :
    Tendsto (fun I : Finset ℕ => I.product I) atTop atTop := by
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

theorem cosine_energy_tendsto (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    Tendsto (fun I : Finset ℕ => ∑ i ∈ I, ∑ j ∈ I, cosineEnergyTerm v (i,j))
      atTop (𝓝 (∑' p : ℕ × ℕ, cosineEnergyTerm v p)) := by
  have h := (cosine_energy_summable v hv).hasSum.comp tendsto_finset_square
  simpa only [Function.comp_def, Finset.product_eq_sprod, sum_product] using h

noncomputable def cosineH2Form (v : ℕ → ℂ) : ℝ :=
  (∑' p : ℕ × ℕ, cosineEnergyTerm v p).re

theorem cosine_h2_form_dissipative (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    cosineH2Form v ≤ -(21/4:ℝ)*(∑' j : ℕ, ‖v j‖^2) := by
  have henergy : Tendsto
      (fun I : Finset ℕ => (∑ i ∈ I, ∑ j ∈ I, cosineEnergyTerm v (i,j)).re)
      atTop (𝓝 (cosineH2Form v)) :=
    (Complex.continuous_re.tendsto _).comp (cosine_energy_tendsto v hv)
  have hmass : Tendsto (fun I : Finset ℕ => ∑ j ∈ I, ‖v j‖^2)
      atTop (𝓝 (∑' j : ℕ, ‖v j‖^2)) := (h2_coefficients_mass_summable v hv).hasSum
  apply le_of_tendsto_of_tendsto' henergy (hmass.const_mul (-(21/4:ℝ)))
  intro I
  simpa only [cosineEnergyTerm] using cosine_finite_form_dissipative I v

end Lemniscate.CoarseArithmetic
