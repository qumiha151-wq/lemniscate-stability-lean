import SolitonClassification.FrozenEndpointConsequences
import SolitonClassification.FrozenActualSection
import SolitonClassification.ContinuousScattering

noncomputable section
namespace ClosedSimilarity.FrozenStress.Endpoint
open GlobalSupport Set Filter
open scoped Topology

/-- A single fixed curvature gives vanishing transverse stress on both ends
    of one complete orbit, including the unnormalized stress component. -/
theorem TerminalBounds.zero_scattering_orbit (h : TerminalBounds) :
    ∃ c ∈ Ioo (-1/4 : ℝ) 1,
      Tendsto (seam c).rawI atTop (𝓝 0) ∧ Tendsto (seam c).rawI atBot (𝓝 0) ∧
      Tendsto (seam c).transverse atTop (𝓝 0) ∧ Tendsto (seam c).transverse atBot (𝓝 0) ∧
      ∀ s : ℝ, 12 ≤ -(seam c).radial s → ((seam c).transverse s)^2*(-(seam c).radial s) ≤ 128 := by
  have margins (t : ℝ) (ht : 20 ≤ t) := h.both_tails t (ht.trans (le_abs_self t))
  obtain ⟨c,hc,ht,hb⟩ := exists_zero_scattering (a := -1/4) (b := 1) (m := -0.002) (n := 0.52)
    (by norm_num) (by norm_num) (by norm_num)
    ((eventually_ge_atTop (20:ℝ)).mono fun s hs => (margins s hs).1.le)
    ((eventually_ge_atTop (20:ℝ)).mono fun s hs => (margins s hs).2.le)
  obtain ⟨_,hv,hp,hq⟩ := seam_initial c
  have hr : (seam c).radial 0 = 0 := by simp [Orbit.radial,hv,hq]
  have raw := (seam c).transverse_tendsto_of_zero hr hp ht
  have even (s : ℝ) : (seam c).transverse (-s) = (seam c).transverse s := by
    obtain ⟨k,v,p,q⟩ := (seam c).seam_reflection hv hq s
    simp [Orbit.transverse,k,v,p,q]
  exact ⟨c,hc,ht,hb,raw,(raw.comp tendsto_neg_atBot_atTop).congr even,
    (fun s hs => (seam c).transverse_decay_at_zero ht hs)⟩

/-- Every height beyond one common threshold realizes the entire interval
    of impacts at paired sections along the corresponding physical-clock
    trajectories of the frozen system. -/
theorem TerminalBounds.all_high_sections (h : TerminalBounds) :
    ∃ S≥20, ∃ H₀ : ℝ, ∀ H≥H₀, ∃ w : SeamSection (-1/4) 1 S H,
      ∀ v ∈ Icc (-0.002:ℝ) 0.52, ∃ c : Icc (-1/4:ℝ) 1, (c:ℝ)∈Ioo (-1/4) 1 ∧
        seamImpact c (-w.time c) = v ∧ seamImpact c (w.time c) = v := by
  obtain ⟨S,hS,H₀,entry⟩ := actual_seam_sections (-1/4) 1
  refine ⟨S,hS,H₀,fun H high => ?_⟩
  obtain ⟨w⟩ := entry H high
  exact ⟨w,fun _ hv => w.realizes_interval (by norm_num)
    (fun t ht => (h.both_tails t ((hS.trans ht).trans (le_abs_self t))).1)
    (fun t ht => (h.both_tails t ((hS.trans ht).trans (le_abs_self t))).2) hv⟩

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.TerminalBounds.zero_scattering_orbit
#print axioms ClosedSimilarity.FrozenStress.Endpoint.TerminalBounds.all_high_sections
