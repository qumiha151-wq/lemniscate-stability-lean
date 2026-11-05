import Lemniscate.PeriodicSobolevClassicalJet

/-! All integer Sobolev representatives give the same smooth periodic curve. -/
noncomputable section
namespace Lemniscate
open scoped ContDiff

/-- Continuous values admitting representatives in every Sobolev order
have a smooth periodic lift, with no bound on their higher norms. -/
theorem circle_smooth_of_all_sobolev_lifts (T : ℝ) [Fact (0<T)]
    (f : C(AddCircle T,ℂ))
    (hreg : ∀ n : ℕ, ∃ u : CircleSobolevSpace T (n+1),
      circleSobolevCoordinate T (n+1) 0 u=circleContinuousL2 T f) :
    ContDiff ℝ ∞ (fun x : ℝ => f (x:AddCircle T)) := by
  apply contDiff_infty.mpr
  intro n
  obtain ⟨u,hu⟩ := hreg n
  have hvalue : circleSobolevClassicalJet T n u 0=f := by
    apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
    change circleContinuousL2 T (circleSobolevClassicalJet T n u 0)=circleContinuousL2 T f
    exact (circle_sobolev_classical_jet_l2 T n u 0).trans hu
  simpa only [hvalue] using (circle_sobolev_classical_regularity T n u).1

end Lemniscate
