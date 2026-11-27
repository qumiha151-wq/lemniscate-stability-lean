import BernoulliBridge.BernoulliAllTimeGraph
import BernoulliBridge.BernoulliGraphDisk

noncomputable section
namespace Lemniscate
open Set MeasureTheory Complex MigrationGeometry
open scoped ContDiff

/-- Smooth parametrized physical solutions, including the initial endpoint. -/
def BernoulliBridgeSolution (γ₀ : ℝ → ℂ) (Y : ℝ → ℝ → ℂ) : Prop :=
  ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => Y z.1 z.2) (Ici (0:ℝ) ×ˢ univ) ∧
  (∀ t,0≤t → Function.Periodic (Y t) (2*Real.pi)) ∧ IsFreeElasticFlow Y ∧
  ∀ s,Y 0 s=γ₀ s

private theorem scale_monotone_from_initial {a t : ℝ} (ha : 0<a) (ht : 0≤t) :
    a≤(a^4+30*t)^(1/4:ℝ) := by
  calc
    a = (a^4)^(1/4:ℝ) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul ha.le]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (pow_nonneg ha.le _) (by linarith) (by norm_num)

/-- For any fixed cover and any target fraction below the exact reference
inradius, intrinsic small initial curvature deviation supplies one common center
and a disk in every physical hull from time zero. The initial neighborhood
depends on the cover and on the chosen radius. -/
theorem bernoulli_nonmigration_from_initial_curvature :
    ∃ e : ℝ ≃o ℝ,(∀ u,e u=∫ t in (0:ℝ)..u,Real.sqrt 2*‖bernoulliVelocity t‖) ∧
    ∀ M : ℕ,0<M → ∀ r : ℝ,0<r → r<BernoulliDisk.radius → ∃ ε>0,∀ γ₀ : ℝ → ℂ,
    ContDiff ℝ ∞ γ₀ → Function.Periodic γ₀ (2*Real.pi) →
    (∀ u,deriv γ₀ u≠0) → lemniscateCurvatureDeviation e M γ₀<ε →
    let a := lemniscateInitialScale M γ₀
    0<a ∧ (∃ Y,BernoulliBridgeSolution γ₀ Y) ∧ ∃ p : ℂ,∀ Y,BernoulliBridgeSolution γ₀ Y →
      (∀ t,0≤t → Metric.closedBall p ((a^4+30*t)^(1/4:ℝ)*r) ⊆ convexHull ℝ (range (Y t))) ∧
      (∀ t,0≤t → Metric.closedBall p (a*r) ⊆ convexHull ℝ (range (Y t))) ∧
      (∀ s,0≤s → ∀ t,0≤t → ¬SimilarityHull.separated (range (Y s)) (range (Y t))) := by
  obtain ⟨e,he,_,graph⟩ := bernoulli_all_time_graph_from_initial_curvature
  obtain ⟨e',he',_,stability⟩ := lemniscate_stability
  have same : e'=e := by
    ext u
    rw [he',he]
  subst e'
  refine ⟨e,he,?_⟩
  intro M hM r hr hmax
  let d := BernoulliDisk.radius-r
  have hd : 0<d := sub_pos.mpr hmax
  have hcut : d<BernoulliDisk.radius := by dsimp [d]; linarith
  obtain ⟨εGraph,hεGraph,hgraph⟩ := graph M hM d hd
  obtain ⟨εFlow,hεFlow,A,B,_,hflow⟩ := stability M hM
  refine ⟨min εGraph εFlow,lt_min hεGraph hεFlow,?_⟩
  intro γ₀ smooth per reg hdev
  obtain ⟨ha,p,hp⟩ := hgraph γ₀ smooth per reg (hdev.trans_le (min_le_left _ _))
  obtain ⟨Y₀,hY₀,initial₀,smooth₀,per₀,_⟩ :=
    (hflow γ₀ smooth per reg (hdev.trans_le (min_le_right _ _))).1
  refine ⟨ha,⟨Y₀,smooth₀,per₀,hY₀,initial₀⟩,p,?_⟩
  rintro Y ⟨hY,periodic,flow,initial⟩
  let a := lemniscateInitialScale M γ₀
  let ρ := fun t : ℝ => (a^4+30*t)^(1/4:ℝ)
  have hscale (t : ℝ) (ht : 0≤t) : a≤ρ t := scale_monotone_from_initial ha ht
  have growing (t : ℝ) (ht : 0≤t) : Metric.closedBall p (ρ t*r) ⊆ convexHull ℝ (range (Y t)) := by
    obtain ⟨α,h,height,orbit⟩ := hp Y hY periodic flow initial t ht
    have hslice : ContDiff ℝ ∞ (Y t) := by
      apply contDiffOn_univ.mp
      exact hY.comp (contDiffOn_const.prodMk contDiffOn_id) (fun s _ => ⟨ht,mem_univ s⟩)
    have disk := bernoulli_oriented_graph_disk_of_height e he h p α (ρ t) (lemniscateLength M)
      d (ha.trans_le (hscale t ht)) hcut height (Y t) hslice.continuous (periodic t ht) orbit
    rwa [show BernoulliDisk.radius-d=r by dsimp [d]; ring] at disk
  have common (t : ℝ) (ht : 0≤t) : Metric.closedBall p (a*r) ⊆ convexHull ℝ (range (Y t)) :=
    (Metric.closedBall_subset_closedBall (mul_le_mul_of_nonneg_right (hscale t ht) hr.le)).trans (growing t ht)
  have center : p ∈ Metric.closedBall p (a*r) := Metric.mem_closedBall.mpr (by
    rw [dist_self]
    exact (mul_pos ha hr).le)
  exact ⟨growing,common,fun s hs t ht =>
    SimilarityHull.not_separated_of_common_hull (common s hs center) (common t ht center)⟩

end Lemniscate
#print axioms Lemniscate.bernoulli_nonmigration_from_initial_curvature
