import Migration.SimilarityHull
import Migration.SimilarityClock

noncomputable section
open Set
open MigrationGeometry.SimilarityHull MigrationGeometry.SimilarityClock

namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- Physical position after one full parameter period. -/
def similaritySlice (t : ℝ) : Set ℂ := c.position t '' Icc 0 c.period

/-- Similarity of the actual material positions, allowing a different
surjective change of parameter on the universal cover at each time. -/
def HasMaterialSimilarity (O : ℂ) (radius angle : ℝ → ℝ) : Prop :=
  ∀ t, 0≤t → ∃ ψ : ℝ → ℝ, Function.Surjective ψ ∧ ∀u,
    c.position t u = O + (radius t : ℂ) *
      ((Real.cos (angle t) : ℂ) + (Real.sin (angle t) : ℂ)*Complex.I) *
      (c.position 0 (ψ u) - O)

private theorem similaritySlice_eq_range {t : ℝ}
    (hp : Function.Periodic (c.position t) c.period) :
    c.similaritySlice t = range (c.position t) := by
  apply Set.Subset.antisymm
  · rintro z ⟨u,_,rfl⟩
    exact ⟨u,rfl⟩
  · rintro z ⟨u,rfl⟩
    obtain ⟨v,hv,he⟩ := hp.exists_mem_Ico₀ c.period_pos u
    exact ⟨v,⟨hv.1,hv.2.le⟩,he.symm⟩

theorem similaritySlice_eq_image {O : ℂ} {a b : ℝ} {radius angle : ℝ → ℝ}
    (rate : Rates a b radius angle) (form : c.HasMaterialSimilarity O radius angle)
    (hper : ∀t, 0≤t → Function.Periodic (c.position t) c.period)
    {t : ℝ} (ht : 0≤t) :
    c.similaritySlice t = sim O b (clock a t) '' c.similaritySlice 0 := by
  obtain ⟨ψ,hψ,model⟩ := form t ht
  obtain ⟨hr,hθ⟩ := rate.solution ht
  have pos (u : ℝ) : c.position t u = sim O b (clock a t) (c.position 0 (ψ u)) := by
    simpa only [sim,hr,hθ] using model u
  rw [c.similaritySlice_eq_range (hper t ht),c.similaritySlice_eq_range (hper 0 le_rfl)]
  ext z
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨_,⟨ψ u,rfl⟩,(pos u).symm⟩
  · rintro ⟨_,⟨v,rfl⟩,rfl⟩
    obtain ⟨u,rfl⟩ := hψ v
    exact ⟨u,pos u⟩

private theorem periodic_forward_slices
    (hdom : Ioi (0:ℝ) ⊆ I) (hp : Function.Periodic (c.position 0) c.period)
    (t : ℝ) (ht : 0≤t) : Function.Periodic (c.position t) c.period := by
  rcases ht.eq_or_lt with h|h
  · simpa [←h] using hp
  · exact c.periodic t (hdom h)

/-- The earlier image can be required to be the given initial curve. -/
theorem physical_initial_similarity_migration_iff {O : ℂ} {a b : ℝ} (ha : 0<a)
    {radius angle : ℝ → ℝ} (rate : Rates a b radius angle)
    (form : c.HasMaterialSimilarity O radius angle)
    (hdom : Ioi (0:ℝ) ⊆ I) (hc : Continuous (c.position 0))
    (hp : Function.Periodic (c.position 0) c.period) :
    (∃ t : ℝ, 0<t ∧ separated (c.similaritySlice 0) (c.similaritySlice t)) ↔
      O ∉ convexHull ℝ (c.similaritySlice 0) := by
  have per := c.periodic_forward_slices hdom hp
  have K : IsCompact (c.similaritySlice 0) := isCompact_Icc.image hc
  have ne : (c.similaritySlice 0).Nonempty :=
    ⟨_,0,⟨le_rfl,c.period_pos.le⟩,rfl⟩
  rw [←separated_initial_log_slice_iff K ne O b]
  constructor
  · rintro ⟨t,ht,sep⟩
    have pos := clock_lt ha (le_rfl : (0:ℝ)≤0) ht
    have zero : clock a 0=0 := by simp [clock]
    refine ⟨clock a t,zero ▸ pos,?_⟩
    rwa [←c.similaritySlice_eq_image rate form per ht.le]
  · rintro ⟨v,hv,sep⟩
    have pos := elapsed_lt ha hv
    have zero : elapsed a 0=0 := by simp [elapsed]
    refine ⟨elapsed a v,zero ▸ pos,?_⟩
    rw [c.similaritySlice_eq_image rate form per (elapsed_nonneg ha hv.le),clock_elapsed ha]
    exact sep

/-- For a forward self-similar immersion, two actual physical-time images
can occupy opposite strict half-planes precisely when the centre lies
outside the convex hull of the initial image. This kinematic implication
applies in particular to normal free elastic flows with these rates. -/
theorem physical_similarity_migration_iff {O : ℂ} {a b : ℝ} (ha : 0<a)
    {radius angle : ℝ → ℝ} (rate : Rates a b radius angle)
    (form : c.HasMaterialSimilarity O radius angle)
    (hdom : Ioi (0:ℝ) ⊆ I) (hc : Continuous (c.position 0))
    (hp : Function.Periodic (c.position 0) c.period) :
    (∃ s t : ℝ, 0≤s ∧ s<t ∧ separated (c.similaritySlice s) (c.similaritySlice t)) ↔
      O ∉ convexHull ℝ (c.similaritySlice 0) := by
  have per := c.periodic_forward_slices hdom hp
  have K : IsCompact (c.similaritySlice 0) := isCompact_Icc.image hc
  have ne : (c.similaritySlice 0).Nonempty :=
    ⟨_,0,⟨le_rfl,c.period_pos.le⟩,rfl⟩
  rw [←separated_log_slices_iff K ne O b]
  constructor
  · rintro ⟨s,t,hs,hst,sep⟩
    refine ⟨clock a s,clock a t,clock_nonneg ha hs,clock_lt ha hs hst,?_⟩
    simpa only [c.similaritySlice_eq_image rate form per hs,
      c.similaritySlice_eq_image rate form per (hs.trans hst.le)] using sep
  · rintro ⟨u,v,hu,huv,sep⟩
    have hs := elapsed_nonneg ha hu
    have ht := elapsed_nonneg ha (hu.trans huv.le)
    refine ⟨elapsed a u,elapsed a v,hs,elapsed_lt ha huv,?_⟩
    rw [c.similaritySlice_eq_image rate form per hs,c.similaritySlice_eq_image rate form per ht,
      clock_elapsed ha,clock_elapsed ha]
    exact sep

#print axioms physical_similarity_migration_iff
#print axioms physical_initial_similarity_migration_iff
end MigrationGeometry.Flow.SmoothPeriodicImmersion
