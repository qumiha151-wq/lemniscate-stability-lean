import Lemniscate.PhysicalNormalization

/-! The physical scale formula determines its derivatives at positive
times, independently of how the scale was extended to negative times. -/
noncomputable section
namespace Lemniscate
open Filter Set
open scoped Topology

/-- Any scale with the exact fourth-root formula on nonnegative times
has the actual normalization derivatives at every positive time. -/
theorem physical_normalization_derivatives_of_formula
    (a : ℝ) (ha : 0<a) (ρ : ℝ → ℝ)
    (hρ : ∀ t : ℝ,0≤t → ρ t=(a^4+30*t)^(1/4:ℝ)) :
    ∀ t : ℝ,0<t →
      HasDerivAt ρ ((15/2:ℝ)*(ρ t)⁻¹^3) t ∧
      HasDerivAt (normalizedTime a) ((ρ t)⁻¹^4) t := by
  obtain ⟨ρ₀,_,_,hρ₀,_,_⟩ := physical_normalization a ha
  intro t ht
  have heq (s : ℝ) (hs : 0≤s) : ρ₀ s=ρ s :=
    (hρ₀ s hs).2.1.trans (hρ s hs).symm
  have hgerm : ρ₀=ᶠ[𝓝 t] ρ := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact heq s hs.le
  have hdata := hρ₀ t ht.le
  have hd : HasDerivAt ρ ((15/2:ℝ)*(ρ₀ t)⁻¹^3) t :=
    hdata.2.2.2.2.1.congr_of_eventuallyEq hgerm.symm
  exact ⟨by simpa only [heq t ht.le] using hd,
    by simpa only [heq t ht.le] using hdata.2.2.2.2.2⟩

end Lemniscate
