import Migration.DiskDissipation
import Migration.EscapingHulls
import Migration.SimilarityFlow

noncomputable section
open Set
open MigrationGeometry.SimilarityHull
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- The geometric image at each positive time is obtained by some
orientation-preserving similarity about O. No time law, asymptotic
expansion assumption or choice of material labels is required. -/
def HasCenteredSimilarityImages (O : ℂ) : Prop :=
  ∀ t : ℝ, 0<t → ∃ a : ℂ, c.similaritySlice t = directSimilarity O a '' c.similaritySlice 0

private theorem slice_bound {s : ℝ} (hc : Continuous (c.position s)) (O : ℂ) :
    ∃ M : ℝ, 0≤M ∧ ∀z∈c.similaritySlice s, dist z O≤M := by
  have hk : IsCompact (c.similaritySlice s) := isCompact_Icc.image hc
  have ne : (c.similaritySlice s).Nonempty := ⟨_,0,⟨le_rfl,c.period_pos.le⟩,rfl⟩
  obtain ⟨m,hm,hmax⟩ := hk.exists_isMaxOn ne
    (show ContinuousOn (fun z => dist z O) _ from (continuous_id.dist continuous_const).continuousOn)
  exact ⟨dist m O,dist_nonneg,fun _ hz => hmax hz⟩

/-- A genuine forward free elastic flow that remains similar about a fixed
centre migrates from every prescribed slice to arbitrarily late slices
exactly when the centre lies outside the initial convex hull. -/
theorem actual_self_similar_migration_iff (hf : c.IsNormalFEF) (dom : Ioi (0:ℝ) ⊆ I)
    (hc : Continuous (c.position 0)) (O : ℂ) (shape : c.HasCenteredSimilarityImages O) :
    (∀ s : ℝ, 0≤s → ∀ T : ℝ, ∃ t : ℝ, T<t ∧ s<t ∧
      separated (c.similaritySlice s) (c.similaritySlice t)) ↔
      O ∉ convexHull ℝ (c.similaritySlice 0) := by
  let K := c.similaritySlice 0
  have hk : IsCompact K := isCompact_Icc.image hc
  have ne : K.Nonempty := ⟨_,0,⟨le_rfl,c.period_pos.le⟩,rfl⟩
  constructor
  · intro migrate hO
    obtain ⟨t,ht,_,hsep⟩ := migrate 0 le_rfl 0
    obtain ⟨a,ha⟩ := shape t ht
    rw [ha] at hsep
    exact not_separated_of_common_hull hO (center_mem_direct_hull hO a) hsep
  · intro hO s hs T
    let d := Metric.infDist O (convexHull ℝ K)
    have hd : 0<d := ((compact_convexHull hk).isClosed.notMem_iff_infDist_pos
      (ne.mono (subset_convexHull ℝ K))).mp hO
    obtain ⟨M,hM,cap⟩ := c.slice_bound hc O
    have hcs : Continuous (c.position s) := by
      rcases hs.eq_or_lt with e|p
      · simpa [←e] using hc
      · exact (c.position_slice_smooth (dom p)).continuous
    obtain ⟨R,hR,early⟩ := c.slice_bound hcs O
    let B := (R/d+1)*(M+1)
    have hB : 0<B := by dsimp [B]; positivity
    obtain ⟨t,late,ht,escape⟩ := c.escapes_all_fixed_radii hf dom (max T s) hB
    obtain ⟨u,hu,far⟩ := escape O
    obtain ⟨a,fit⟩ := shape t ht
    have incl : c.position t u ∈ c.similaritySlice t := ⟨u,hu,rfl⟩
    rw [fit] at incl
    obtain ⟨x,hx,eq⟩ := incl
    have nd : ‖c.position t u-O‖ = ‖a‖*dist x O := by
      rw [←eq]
      simp [directSimilarity,dist_eq_norm]
    rw [nd] at far
    have gap : R < ‖a‖*d := by
      by_contra! bad
      have ab : ‖a‖≤R/d := (le_div_iff₀ hd).mpr bad
      have hxm := cap x hx
      have upper := mul_le_mul ab hxm dist_nonneg (div_nonneg hR hd.le)
      dsimp [B] at far
      nlinarith only [upper,far,div_nonneg hR hd.le,hM]
    refine ⟨t,(le_max_left T s).trans_lt late,(le_max_right T s).trans_lt late,?_⟩
    apply separated_of_similarity_error (K:=K) hk O a (R:=R) (ε:=0) early
    · intro y hy
      rw [fit] at hy
      obtain ⟨x,hx,rfl⟩ := hy
      exact ⟨x,hx,le_of_eq (dist_self _)⟩
    · simpa only [add_zero] using gap

/-- The existential form of the original strict two-half-plane question,
with the given initial curve itself on the first side. -/
theorem actual_initial_self_similar_migration_iff (hf : c.IsNormalFEF)
    (dom : Ioi (0:ℝ) ⊆ I) (hc : Continuous (c.position 0)) (O : ℂ)
    (shape : c.HasCenteredSimilarityImages O) :
    (∃ t : ℝ, 0<t ∧ separated (c.similaritySlice 0) (c.similaritySlice t)) ↔
      O ∉ convexHull ℝ (c.similaritySlice 0) := by
  constructor
  · rintro ⟨t,ht,hsep⟩ hO
    obtain ⟨a,ha⟩ := shape t ht
    rw [ha] at hsep
    exact not_separated_of_common_hull hO (center_mem_direct_hull hO a) hsep
  · intro hO
    obtain ⟨t,ht,_,hsep⟩ := (c.actual_self_similar_migration_iff hf dom hc O shape).mpr hO 0 le_rfl 0
    exact ⟨t,ht,hsep⟩

#print axioms actual_self_similar_migration_iff
#print axioms actual_initial_self_similar_migration_iff
end MigrationGeometry.Flow.SmoothPeriodicImmersion
