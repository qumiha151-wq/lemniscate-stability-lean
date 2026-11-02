import Lemniscate.PeriodicBlochCompactResolvent
import Mathlib.Topology.Algebra.Module.LinearPMap

/-! Closedness on the stated H4 domain follows from the actual bounded
two-sided inverse. This avoids a second adjoint-domain regularity argument. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleBlochPMap (h h₁ h₂ : C(AddCircle T, ℂ)) (α : ℝ) :
    CircleL2 T →ₗ.[ℂ] CircleL2 T where
  domain := circleH4Domain T
  toFun := circleBlochOperator T h h₁ h₂ α

theorem circle_bloch_pmap_closed (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : ‖h‖ ≤ 1) (hh₁ : ‖h₁‖ ≤ 2) (hh₂ : ‖h₂‖ ≤ 4)
    (α : ℝ) (hz : ‖(α:ℂ)*circleFrequencyFactor T 1‖ ≤ 1) :
    (circleBlochPMap T h h₁ h₂ α).IsClosed := by
  obtain ⟨r,_,R,_,hR⟩ := circle_bloch_compact_resolvent_exists T h h₁ h₂ hh hh₁ hh₂ α hz
  have hgraph : ((circleBlochPMap T h h₁ h₂ α).graph : Set (CircleL2 T × CircleL2 T)) =
      {v | v.1 = R ((r:ℂ) • v.1-v.2)} := by
    ext v
    change v ∈ (circleBlochPMap T h h₁ h₂ α).graph ↔ v.1 = R ((r:ℂ) • v.1-v.2)
    rw [LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨u,hu,hAu⟩
      change v.1 = R ((r:ℂ) • v.1-v.2)
      rw [← hu,← hAu]
      exact (hR.2 u).symm
    · intro hv
      obtain ⟨u,hu,hshift⟩ := hR.1 ((r:ℂ) • v.1-v.2)
      have hux : (u:CircleL2 T) = v.1 := hu.trans hv.symm
      refine ⟨u,hux,?_⟩
      change (r:ℂ) • (u:CircleL2 T)-circleBlochOperator T h h₁ h₂ α u =
        (r:ℂ) • v.1-v.2 at hshift
      rw [hux] at hshift
      simp only [sub_eq_add_neg] at hshift
      exact neg_injective (add_left_cancel hshift)
  change IsClosed ((circleBlochPMap T h h₁ h₂ α).graph : Set (CircleL2 T × CircleL2 T))
  rw [hgraph]
  exact isClosed_eq continuous_fst
    (R.continuous.comp ((continuous_fst.const_smul (r:ℂ)).sub continuous_snd))

end Lemniscate
