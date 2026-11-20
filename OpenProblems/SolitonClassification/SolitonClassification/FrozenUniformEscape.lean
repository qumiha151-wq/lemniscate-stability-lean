import SolitonClassification.FrozenSeamEscape

noncomputable section
open Set Filter
namespace ClosedSimilarity.FrozenStress

/-- Continuous dependence at fixed times converts pointwise frozen escape into
a common entrance time for any compact family of seam initial data. -/
theorem uniform_seam_entrance {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (Z : X→Orbit) (zero : ∀c,(Z c).radial 0=0) (p0 : ∀c,(Z c).p 0=1)
    (continuous : ∀t : ℝ, Continuous (fun c => (Z c).radial t)) (R : ℝ) :
    ∃T≥0, ∀c t,T≤t → R < -(Z c).radial t := by
  let U : ℝ→Set X := fun t => {c | R < -(Z c).radial t}
  have op (t : ℝ) : IsOpen (U t) := isOpen_lt continuous_const (continuous t).neg
  have cover : (univ : Set X)⊆⋃t,U t := by
    intro c _
    obtain ⟨t,ht⟩ := ((Z c).outgoing_radial_tendsto_atTop (zero c) (p0 c)).eventually_gt_atTop R |>.exists
    exact mem_iUnion.mpr ⟨t,ht⟩
  have inc {s t : ℝ} (st : s≤t) : U s⊆U t := fun c hc =>
    lt_of_lt_of_le hc (neg_le_neg ((Z c).radial_antitone st))
  obtain ⟨t,h⟩ := isCompact_univ.elim_directed_cover U op cover
    (fun s t => ⟨max s t,inc (le_max_left ..),inc (le_max_right ..)⟩)
  exact ⟨max 0 t,le_max_left ..,fun c x hx => inc ((le_max_right 0 t).trans hx) (h (mem_univ c))⟩

end ClosedSimilarity.FrozenStress
#print axioms ClosedSimilarity.FrozenStress.uniform_seam_entrance
