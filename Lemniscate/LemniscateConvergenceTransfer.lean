import Lemniscate.LemniscateStabilityStatement
import Lemniscate.ArclengthOrbitCharacterization

noncomputable section
namespace Lemniscate
open Complex Set Filter
open scoped ContDiff Topology

/-- A single family of actual oriented curve equivalences transfers all
spatial convergence orders and rates with the same center and limiting
rotation. -/
theorem lemniscate_convergence_of_oriented_equivalence
    (e : ℝ ≃o ℝ) (M : ℕ) (γ₀ : ℝ → ℂ)
    (Y Core : ℝ → ℝ → ℂ)
    (εRate CRate : Ioo (0:ℝ) (lemniscateGap M) → ℕ → ℝ)
    (a : ℝ) (ha : 0<a) (haScale : a=lemniscateInitialScale M γ₀)
    (ρ : ℝ → ℝ) (hρ : ∀ t : ℝ,0≤t → ρ t=(a^4+30*t)^(1/4:ℝ))
    (p₀ Rlim : ℂ) (hRlim : ‖Rlim‖=1)
    (hqual : ∀ j : ℕ,Tendsto (fun t : ℝ => periodicCjNorm j
      (fun s : ℝ => Core t s/(ρ t:ℂ)-Rlim*lemniscateReference e s)) atTop (𝓝 0))
    (hrate : ∀ (μ : Ioo (0:ℝ) (lemniscateGap M)) (j : ℕ),
      lemniscateCurvatureDeviation e M γ₀<εRate μ j →
      ∀ t : ℝ,a^4≤t → periodicCjNorm j
        (fun s : ℝ => (Core t s-p₀)/(ρ t:ℂ)-Rlim*lemniscateReference e s)≤
          CRate μ j*(1+30*t/a^4)^(-(μ:ℝ)/30)*
            Real.sqrt (lemniscateCurvatureDeviation e M γ₀))
    (hE : ∀ t : ℝ,0≤t → OrientedCurveEquivalent (Y t) (Core t)
      (2*Real.pi) (lemniscateLength M))
    (hbase : ∀ j : ℕ,∃ C>0,∀ t : ℝ,a^4≤t → periodicCjNorm j
      (fun s : ℝ => (Core t s-p₀)/(ρ t:ℂ)-Rlim*lemniscateReference e s)≤
        C*(1+30*t/a^4)^(-lemniscateGap M/60)) :
    LemniscateScaledConvergence e M γ₀ Y εRate CRate := by
  classical
  let χ : ℝ → (ℝ ≃o ℝ) := fun t =>
    if ht : 0≤t then Classical.choose (hE t ht) else OrderIso.refl ℝ
  have hχ (t : ℝ) (ht : 0≤t) :
      ContDiff ℝ ∞ (χ t : ℝ → ℝ) ∧
      ContDiff ℝ ∞ ((χ t).symm : ℝ → ℝ) ∧
      (∀ s : ℝ,χ t (s+lemniscateLength M)=χ t s+2*Real.pi) ∧
      ∀ s : ℝ,Y t (χ t s)=Core t s := by
    simpa only [χ,dif_pos ht] using! Classical.choose_spec (hE t ht)
  dsimp only [LemniscateScaledConvergence]
  rw [← haScale]
  refine ⟨ha,p₀,Rlim,hRlim,χ,?_,?_,?_,?_⟩
  · intro t ht
    exact ⟨(hχ t ht).1,(hχ t ht).2.1,(hχ t ht).2.2.1⟩
  · intro j
    apply (hqual j).congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    congr 1
    funext s
    rw [(hχ t ht).2.2.2 s,hρ t ht]
  · intro j
    obtain ⟨C,hC,hb⟩ := hbase j
    refine ⟨C,hC,?_⟩
    intro t ht
    have ht₀ : 0≤t := (pow_nonneg ha.le 4).trans ht
    simpa only [(hχ t ht₀).2.2.2,hρ t ht₀] using! hb t ht
  · intro μ j hsmall t ht
    have ht₀ : 0≤t := (pow_nonneg ha.le 4).trans ht
    simpa only [(hχ t ht₀).2.2.2,hρ t ht₀] using! hrate μ j hsmall t ht

end Lemniscate
