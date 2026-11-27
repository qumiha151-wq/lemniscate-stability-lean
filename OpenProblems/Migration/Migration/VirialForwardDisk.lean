import Migration.VirialDriftSlab
import Migration.SublevelMigrationFloor
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
private theorem pi_sq_lt_thirtysix : Real.pi^2<36 := by
  nlinarith only [Real.pi_lt_four,Real.pi_pos,mul_pos (sub_pos.mpr Real.pi_lt_four) (show 0<4+Real.pi by positivity)]
end MigrationGeometry.Flow.SmoothPeriodicImmersion

namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem virial_common_disk_from_positive_initial_data (hf : c.IsNormalFEF)
    {s t : ℝ} (st : s≤t) (slab : Icc s t⊆I)
    (positive : 0<c.signedCurvatureIntegral s)
    (initial : 2*c.bending s*c.coreLength s≤5*Real.pi^2) :
    Metric.closedBall (c.arclengthCentroid s)
      ((80/100)*Real.pi/c.bending s+(2/1000)*Real.pi/c.bending t) ⊆
        convexHull ℝ (c.position t '' Icc 0 c.period) := by
  have cap := c.bending_sublevel_from_initial hf st slab (C:=5*Real.pi^2)
      (by nlinarith [Real.pi_pos]) (by linarith only [pi_sq_lt_thirtysix]) initial
  have winding (v) (hv : v∈Icc s t) :
      c.signedCurvatureIntegral v=2*Real.pi ∨ c.signedCurvatureIntegral v= -(2*Real.pi) := by
    let p := c.materialSlice (slab hv)
    have en : p.bendingCurve.energy=c.bending v := p.bendingCurve_energy
    have leq : p.bendingCurve.period=c.coreLength v := rfl
    have hh : 2*p.bendingCurve.energy*p.bendingCurve.period≤4*Real.pi^2+36 := by
      rw [en,leq]; linarith only [cap v hv,pi_sq_lt_thirtysix]
    have turns := p.bendingCurve.low_product_turning hh
    have eq : (∫a in 0..p.bendingCurve.period,p.bendingCurve.curvature a)=c.signedCurvatureIntegral v := p.bendingCurve_turn
    rwa [eq] at turns
  apply c.virial_common_disk_on_slab hf st slab _ cap
  intro v hv
  rcases winding v hv with h|h
  · exact h
  · have sub : Icc s v⊆Icc s t := Icc_subset_Icc_right hv.2
    obtain ⟨x,hx,eq⟩ := intermediate_value_Icc' hv.1 ((c.scalar_turn_continuous_slab slab).mono sub)
      (show 0∈Icc (c.signedCurvatureIntegral v) (c.signedCurvatureIntegral s) from
        ⟨by rw [h]; linarith only [Real.pi_pos], positive.le⟩)
    rcases winding x (sub hx) with q|q <;> linarith only [q,eq,Real.pi_pos]

end MigrationGeometry.Flow.SmoothPeriodicImmersion
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem virial_common_disk_from_initial_bending (hf : c.IsNormalFEF)
    {s t : ℝ} (st : s≤t) (slab : Icc s t⊆I)
    (initial : 2*c.bending s*c.coreLength s≤5*Real.pi^2) :
    Metric.closedBall (c.arclengthCentroid s)
      ((80/100)*Real.pi/c.bending s+(2/1000)*Real.pi/c.bending t) ⊆
        convexHull ℝ (c.position t '' Icc 0 c.period) := by
  have hs := slab (show s∈Icc s t from ⟨le_rfl,st⟩)
  have ht := slab (show t∈Icc s t from ⟨st,le_rfl⟩)
  let p := c.materialSlice hs
  have en : p.bendingCurve.energy=c.bending s := p.bendingCurve_energy
  have leq : p.bendingCurve.period=c.coreLength s := rfl
  have cap : 2*p.bendingCurve.energy*p.bendingCurve.period≤4*Real.pi^2+36 := by
    rw [en,leq]; linarith only [initial,pi_sq_lt_thirtysix]
  have turns := p.bendingCurve.low_product_turning cap
  have eq : (∫a in 0..p.bendingCurve.period,p.bendingCurve.curvature a)=c.signedCurvatureIntegral s := p.bendingCurve_turn
  rw [eq] at turns
  rcases turns with pos|neg
  · exact c.virial_common_disk_from_positive_initial_data hf st slab (by rw [pos]; positivity) initial
  have init : 2*c.reflected.bending s*c.reflected.coreLength s≤5*Real.pi^2 := by
    rwa [c.reflected_length hs,c.reflected_bending hs]
  have disk := c.reflected.virial_common_disk_from_positive_initial_data (c.reflected_flow hf) st slab
    (by rw [c.reflected_turn hs,neg]; linarith only [Real.pi_pos]) init
  rw [c.reflected_centroid hs,c.reflected_bending hs,c.reflected_bending ht] at disk
  intro z hz
  have dz := Complex.conjLIE.isometry.dist_eq z (c.arclengthCentroid s)
  have zz := disk (show conj z∈_ from Metric.mem_closedBall.mpr (dz.trans_le (Metric.mem_closedBall.mp hz)))
  let A : ℂ→ₗ[ℝ] ℂ := Complex.conjCLE.toLinearEquiv.toLinearMap
  have image_eq : c.reflected.position t '' Icc 0 c.period=A '' (c.position t '' Icc 0 c.period) := by
    rw [Set.image_image]
    rfl
  change conj z ∈convexHull ℝ (c.reflected.position t '' Icc 0 c.period) at zz
  rw [image_eq,← A.image_convexHull] at zz
  obtain ⟨v,hv,h⟩ := zz
  have hvz : v=z := Complex.conjCLE.injective h
  rwa [←hvz]

end MigrationGeometry.Flow.SmoothPeriodicImmersion
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- A disk of fixed positive radius, in the initial laboratory frame, belongs to
all subsequent hulls. The radius uses only the earlier curve's bending energy. -/
theorem virial_persistent_disk_from_initial_bending (hf : c.IsNormalFEF)
    {s t : ℝ} (st : s≤t) (slab : Icc s t⊆I)
    (initial : 2*c.bending s*c.coreLength s≤5*Real.pi^2) :
    Metric.closedBall (c.arclengthCentroid s) ((802/1000)*Real.pi/c.bending s) ⊆
        convexHull ℝ (c.position t '' Icc 0 c.period) := by
  apply Set.Subset.trans (Metric.closedBall_subset_closedBall ?_) (c.virial_common_disk_from_initial_bending hf st slab initial)
  have pos := c.bending_pos_of_width (slab (show t∈Icc s t from ⟨st,le_rfl⟩))
  have leq := c.bending_le_of_slab hf Complex.reCLM st slab
  have h := div_le_div_of_nonneg_left (show 0≤(2/1000)*Real.pi by positivity) pos leq
  calc (802/1000)*Real.pi/c.bending s =
      (80/100)*Real.pi/c.bending s + (2/1000)*Real.pi/c.bending s := by ring
    _ ≤ _ := add_le_add_right h _

end MigrationGeometry.Flow.SmoothPeriodicImmersion
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable (c : SmoothPeriodicImmersion (Ioi 0))

/-- The cap is allowed to hold with equality at a one-sided starting time.
The proof perturbs the threshold rather than assuming an initial derivative. -/
theorem virial_forward_bending_cap (hf : c.IsNormalFEF)
    (energy : ContinuousWithinAt c.bending (Ici 0) 0)
    (len : ContinuousWithinAt c.coreLength (Ici 0) 0)
    (initial : 2*c.bending 0*c.coreLength 0≤5*Real.pi^2)
    {t : ℝ} (ht : 0<t) : 2*c.bending t*c.coreLength t≤5*Real.pi^2 := by
  let U := fun t=>2*c.bending t*c.coreLength t
  let C := 5*Real.pi^2
  let cap := 4*Real.pi^2+36
  have cu : ContinuousWithinAt U (Ioi 0) 0 :=
    ((energy.const_mul 2).mul len).mono Ioi_subset_Ici_self
  by_contra! high
  have hhigh : C<U t := high
  have hh : C<cap := by dsimp [C,cap]; linarith only [pi_sq_lt_thirtysix]
  let M := (C+min (U t) cap)/2
  have greater : C<M := by dsimp only [M]; linarith only [lt_min hhigh hh]
  have smaller : M<min (U t) cap := by dsimp only [M]; linarith only [lt_min hhigh hh]
  have threshold := cu.eventually_lt_const (lt_of_le_of_lt initial greater)
  have time : ∀ᶠ v in 𝓝[>] (0:ℝ), v<t := (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds ht)
  have after : ∀ᶠ v in 𝓝[>] (0:ℝ), 0<v := self_mem_nhdsWithin
  obtain ⟨v,hv,vt,hvM⟩ := (after.and (time.and threshold)).exists
  have slab : Icc v t⊆Ioi 0 := fun x hx=>lt_of_lt_of_le hv hx.1
  have above : 4*Real.pi^2<M := by dsimp [C] at greater; nlinarith [sq_nonneg Real.pi]
  have bd := c.bending_sublevel_from_initial hf vt.le slab above
    (smaller.le.trans (min_le_right _ _)) hvM.le t ⟨vt.le,le_rfl⟩
  exact (not_lt_of_ge bd) (smaller.trans_le (min_le_left _ _))

/-- For a one-sided flow on positive time, every positive-time hull contains
the fixed physical disk based at the initial curve's arclength barycentre. -/
theorem virial_forward_persistent_disk (hf : c.IsNormalFEF)
    (energy : ContinuousWithinAt c.bending (Ici 0) 0)
    (len : ContinuousWithinAt c.coreLength (Ici 0) 0)
    (center : ContinuousWithinAt c.arclengthCentroid (Ici 0) 0)
    (ep : 0<c.bending 0)
    (initial : 2*c.bending 0*c.coreLength 0≤5*Real.pi^2)
    {t : ℝ} (ht : 0<t) :
    Metric.closedBall (c.arclengthCentroid 0) ((802/1000)*Real.pi/c.bending 0) ⊆
      convexHull ℝ (c.position t '' Icc 0 c.period) := by
  let K := convexHull ℝ (c.position t '' Icc 0 c.period)
  have compact : IsCompact K := MigrationGeometry.SimilarityHull.compact_convexHull
      (isCompact_Icc.image (c.position_slice_smooth ht).continuous)
  intro z hz
  let z' := fun v=>c.arclengthCentroid v+(c.bending 0/c.bending v) • (z-c.arclengthCentroid 0)
  have inc : Ioi (0:ℝ)⊆Ici 0 := Ioi_subset_Ici_self
  have cl : Tendsto z' (𝓝[>] 0) (𝓝 z) := by
    have h := (center.mono inc).tendsto.add (((tendsto_const_nhds (x:=c.bending 0)).div
       (energy.mono inc).tendsto ep.ne').smul (tendsto_const_nhds (x:=z-c.arclengthCentroid 0)))
    simpa [z',div_self ep.ne'] using h
  apply compact.isClosed.mem_of_tendsto cl
  have time : ∀ᶠ v in 𝓝[>] (0:ℝ), v<t := (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds ht)
  filter_upwards [self_mem_nhdsWithin,time] with v (hv : 0<v) vt
  have ev := c.bending_pos_of_width hv
  apply c.virial_persistent_disk_from_initial_bending hf vt.le (fun x hx=>lt_of_lt_of_le hv hx.1)
    (c.virial_forward_bending_cap hf energy len initial hv)
  rw [Metric.mem_closedBall,dist_eq_norm] at hz ⊢
  dsimp only [z']
  rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos ep ev)]
  calc c.bending 0 / c.bending v * ‖z-c.arclengthCentroid 0‖ ≤
      c.bending 0/c.bending v * ((802/1000)*Real.pi/c.bending 0) :=
        mul_le_mul_of_nonneg_left hz (div_pos ep ev).le
    _ = _ := by field_simp [ep.ne']

end MigrationGeometry.Flow.SmoothPeriodicImmersion
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable (c : SmoothPeriodicImmersion (Ioi 0))

private theorem virial_initial_hull_of_later_membership
    (position : ContinuousOn (fun q : ℝ×ℝ=>c.position q.1 q.2) (Ici 0×ˢuniv))
    {z : ℂ} (later : ∀v : ℝ, 0<v → z∈convexHull ℝ (c.position v '' Icc 0 c.period)) :
    z∈convexHull ℝ (c.position 0 '' Icc 0 c.period) := by
  have jc : Continuous (fun q : ℝ×ℝ=>c.position (max q.1 0) q.2) :=
    position.comp_continuous ((continuous_fst.max continuous_const).prodMk continuous_snd)
      (fun q=>⟨show 0≤max q.1 0 from le_max_right _ _,mem_univ _⟩)
  have zero : Continuous (c.position 0) := by
    simpa [Function.comp_def] using jc.comp ((continuous_const :
      Continuous (fun _ : ℝ=>(0:ℝ))).prodMk continuous_id)
  let K := c.position 0 '' Icc 0 c.period
  by_contra out
  obtain ⟨H,r,low,high⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ K)
    (MigrationGeometry.SimilarityHull.compact_convexHull (isCompact_Icc.image zero)).isClosed out
  let f := fun (v u : ℝ)=>H (c.position (max v 0) u)
  let supAt := fun v=>sSup (f v '' Icc 0 c.period)
  have cf : Continuous (Function.uncurry f) := H.continuous.comp jc
  have cs : Continuous supAt := isCompact_Icc.continuous_sSup cf
  have maxpt (v : ℝ) := isCompact_Icc.exists_sSup_image_eq_and_ge
    (show (Icc (0:ℝ) c.period).Nonempty from ⟨0,le_rfl,c.period_pos.le⟩)
    (show Continuous (f v) from cf.comp (.prodMk_right v)).continuousOn
  have now : supAt 0<r := by
    obtain ⟨u,hu,h,_⟩ := maxpt 0
    change sSup (f 0 '' Icc 0 c.period)<r
    rw [h]
    simpa [f] using low (c.position 0 u) (subset_convexHull ℝ K ⟨u,hu,rfl⟩)
  have ev : ∀ᶠ v in 𝓝[>] (0:ℝ), H z≤supAt v := by
    filter_upwards [self_mem_nhdsWithin] with v (hv : 0<v)
    let B := {w : ℂ | H w≤supAt v}
    have cap : c.position v '' Icc 0 c.period ⊆ B := by
      rintro _ ⟨u,hu,rfl⟩
      obtain ⟨y,_,eq,m⟩ := maxpt v
      change H (c.position v u)≤sSup (f v '' Icc 0 c.period)
      rw [eq]
      simpa [f,max_eq_left hv.le] using m u hu
    exact (convexHull_min cap (convex_halfSpace_le H.toLinearMap.isLinear _)) (later v hv)
  have hz := le_of_tendsto_of_tendsto tendsto_const_nhds
    (cs.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ev
  linarith

/-- The initial curve and every positive-time curve have an explicit
common disk even when smooth time evolution is only specified for t>0. -/
theorem virial_forward_all_hulls_common_disk (hf : c.IsNormalFEF)
    (position : ContinuousOn (fun q : ℝ×ℝ=>c.position q.1 q.2) (Ici 0×ˢuniv))
    (energy : ContinuousWithinAt c.bending (Ici 0) 0)
    (len : ContinuousWithinAt c.coreLength (Ici 0) 0)
    (center : ContinuousWithinAt c.arclengthCentroid (Ici 0) 0)
    (ep : 0<c.bending 0)
    (initial : 2*c.bending 0*c.coreLength 0≤5*Real.pi^2)
    {t : ℝ} (ht : 0≤t) :
    Metric.closedBall (c.arclengthCentroid 0) ((802/1000)*Real.pi/c.bending 0) ⊆
      convexHull ℝ (c.position t '' Icc 0 c.period) := by
  intro z hz
  have later (v : ℝ) (hv : 0<v) := c.virial_forward_persistent_disk hf energy len center ep initial hv hz
  rcases eq_or_lt_of_le ht with rfl|pos
  · exact c.virial_initial_hull_of_later_membership position later
  · exact later t pos

end MigrationGeometry.Flow.SmoothPeriodicImmersion
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable (c : SmoothPeriodicImmersion (Ioi 0))

private theorem virial_initial_integral_continuity {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (f : ℝ→ℝ→V)
    (hf : ContinuousOn (fun q : ℝ×ℝ=>f q.1 q.2) (Ici 0×ˢuniv)) (p : ℝ) :
    ContinuousWithinAt (fun t=>∫u in 0..p,f t u) (Ici 0) 0 := by
  have cc : Continuous (fun q : ℝ×ℝ=>f (max q.1 0) q.2) :=
    hf.comp_continuous ((continuous_fst.max continuous_const).prodMk continuous_snd)
      (fun q=>⟨show 0≤max q.1 0 from le_max_right _ _,mem_univ _⟩)
  have ci := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ:=volume) (f:=fun t u=>f (max t 0) u) cc 0 p
  have onK : ContinuousOn (fun t=>∫u in 0..p,f t u) (Ici 0) := ci.continuousOn.congr
    (fun t ht=>by simp only [max_eq_left (show 0≤t from ht)])
  exact onK 0 (show (0:ℝ)≤0 from le_rfl)

/-- Classical one-sided initial data: the physical position, speed and curvature
are jointly continuous down to time zero, and the initial curve is immersed. -/
theorem virial_classical_forward_initial_disk (hf : c.IsNormalFEF)
    (position : ContinuousOn (fun q : ℝ×ℝ=>c.position q.1 q.2) (Ici 0×ˢuniv))
    (spd : ContinuousOn (fun q : ℝ×ℝ=>speed (c.position q.1) q.2) (Ici 0×ˢuniv))
    (curv : ContinuousOn (fun q : ℝ×ℝ=>curvature (c.position q.1) q.2) (Ici 0×ˢuniv))
    (regular : ∀u,deriv (c.position 0) u≠0)
    (initial : 2*c.bending 0*c.coreLength 0≤5*Real.pi^2)
    {t : ℝ} (ht : 0≤t) :
    Metric.closedBall (c.arclengthCentroid 0) ((802/1000)*Real.pi/c.bending 0) ⊆
      convexHull ℝ (c.position t '' Icc 0 c.period) := by
  have en : ContinuousWithinAt c.bending (Ici 0) 0 :=
    (virial_initial_integral_continuity (fun t u=>curvature (c.position t) u^2*speed (c.position t) u)
      ((curv.pow 2).mul spd) c.period).div_const _
  have len : ContinuousWithinAt c.coreLength (Ici 0) 0 :=
    virial_initial_integral_continuity (fun t u=>speed (c.position t) u) spd c.period
  have mom := virial_initial_integral_continuity (fun t u=>speed (c.position t) u • c.position t u)
      (spd.smul position) c.period
  have sc : Continuous (fun u=>speed (c.position 0) u) :=
    spd.comp_continuous (continuous_const.prodMk continuous_id) (fun _=>⟨by simp,mem_univ _⟩)
  have lp : 0<c.coreLength 0 := by
    apply intervalIntegral.integral_pos c.period_pos sc.continuousOn
    · exact fun u _=>(speed_pos regular u).le
    · exact ⟨0,⟨le_rfl,c.period_pos.le⟩,speed_pos regular 0⟩
  have cen : ContinuousWithinAt c.arclengthCentroid (Ici 0) 0 :=
    (len.inv₀ lp.ne').smul mom
  have ev : ∀ᶠ v in 𝓝[>] (0:ℝ), c.bending 1≤c.bending v := by
    have small : ∀ᶠ v in 𝓝[>] (0:ℝ), v<1 := (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds zero_lt_one)
    filter_upwards [self_mem_nhdsWithin,small] with v (hv : 0<v) h1
    exact c.bending_le_of_slab hf Complex.reCLM h1.le (fun _ h=>lt_of_lt_of_le hv h.1)
  have ep := lt_of_lt_of_le (c.bending_pos_of_width (show (1:ℝ)∈Ioi 0 by norm_num))
    (le_of_tendsto_of_tendsto tendsto_const_nhds (en.mono Ioi_subset_Ici_self).tendsto ev)
  exact c.virial_forward_all_hulls_common_disk hf position en len cen ep initial ht

end MigrationGeometry.Flow.SmoothPeriodicImmersion
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable (c : SmoothPeriodicImmersion (Ioi 0))

/-- If two material traces of a classical forward flow lie in opposite
open half-planes, its initial normalized bending energy exceeds this floor. -/
theorem virial_migration_requires_initial_bending (hf : c.IsNormalFEF)
    (position : ContinuousOn (fun q : ℝ×ℝ=>c.position q.1 q.2) (Ici 0×ˢuniv))
    (spd : ContinuousOn (fun q : ℝ×ℝ=>speed (c.position q.1) q.2) (Ici 0×ˢuniv))
    (curv : ContinuousOn (fun q : ℝ×ℝ=>curvature (c.position q.1) q.2) (Ici 0×ˢuniv))
    (regular : ∀u,deriv (c.position 0) u≠0)
    {s t : ℝ} (hs : 0≤s) (ht : 0≤t)
    (migration : SimilarityHull.separated (c.position s '' Icc 0 c.period) (c.position t '' Icc 0 c.period)) :
    5*Real.pi^2 < 2*c.bending 0*c.coreLength 0 := by
  by_contra! initial
  have hrad : 0≤(802/1000)*Real.pi/c.bending 0 := by
    have := c.bending_nonneg 0
    positivity
  have center := Metric.mem_closedBall_self (x:=c.arclengthCentroid 0) hrad
  exact SimilarityHull.not_separated_of_common_hull
    (c.virial_classical_forward_initial_disk hf position spd curv regular initial hs center)
    (c.virial_classical_forward_initial_disk hf position spd curv regular initial ht center) migration

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.virial_migration_requires_initial_bending
