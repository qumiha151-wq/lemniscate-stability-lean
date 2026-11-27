import Migration.HullGapGeometry
import Migration.HullFrameWindow
import Migration.HullCompactGap

noncomputable section
open Set Filter
open scoped Topology
namespace MigrationGeometry.HullGap
open Adjoint

theorem uniform_frame_gap : ∃ ε>0, ∀ (L : ℝ), 0<L → ∀ (f : Frame 1 L),
    (∀ s, ((f.p s)^2+(f.q s)^2)^2≤2+ε) →
    (∀ s, (f.u s)^2+(f.n s)^2=1) → ∃ s∈Icc 0 L, f.h s < -ε := by
  classical
  by_contra! bad
  let e := fun n : ℕ => (1/2:ℝ)^n
  have ep (n : ℕ) : 0<e n := by dsimp [e]; positivity
  have e1 (n : ℕ) : e n≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  choose L Lp f radi unit height using fun n => bad (e n) (ep n)
  let Z := fun n => frameState (f n)
  have per (i : ℕ) : Function.Periodic (Z i) (L i) := frameState_periodic _
  have cs (i : ℕ) : Continuous (Z i) :=
    continuous_iff_continuousAt.mpr fun s => (frameState_d (f i) s).continuousAt
  choose m hm maxm using fun i : ℕ => isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (Lp i).le)
    (((continuous_apply (7:Fin 8)).comp (cs i)).continuousOn)
  let Y := fun i t => Z i (t+m i)
  have ym (i : ℕ) (t : ℝ) : Y i t 7≤Y i 0 7 := by
    obtain ⟨w,hw,eq⟩ := (per i).exists_mem_Ico₀ (Lp i) (t+m i)
    simpa only [Y,zero_add,eq] using (show Z i (t+m i) 7≤Z i (m i) 7 by
      rw [eq]; exact maxm i (Ico_subset_Icc_self hw))
  have yh (i : ℕ) (t : ℝ) : -e i≤Y i t 4 := by
    obtain ⟨w,hw,eq⟩ := (per i).exists_mem_Ico₀ (Lp i) (t+m i)
    change -e i≤Z i (t+m i) 4
    rw [eq]
    exact height i w (Ico_subset_Icc_self hw)
  have rad2 (i : ℕ) (t : ℝ) : ((f i).p t)^2+((f i).q t)^2≤4 := by
    apply le_of_sq_le_sq _ (by norm_num)
    linarith only [radi i t,e1 i]
  obtain ⟨K,Kcap⟩ := uniform_frame_bound
  have dy (i : ℕ) (t : ℝ) : HasDerivAt (Y i) (velocity (Y i t)) t :=
    (frameState_d (f i) (t+m i)).comp_add_const t (m i)
  exact no_near_critical_sequence velocity_smooth Y K e
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/2:ℝ)) (by norm_num))
    dy (fun i t => Kcap (f i) (rad2 i) (unit i) (t+m i))
    (fun i t => radi i (t+m i)) (fun i t => unit i (t+m i)) yh ym

/-- Uniform centred disk containment for actual profiles of any positive rate,
    with a radius threshold strictly larger than the pointwise bound two. -/
theorem uniform_expander_hull_disk : ∃ δ>0, ∃ η>0, ∀ (a L : ℝ), 0<a → 0<L →
    ∀ (c : ClosedExpander (a^4) L), (∀ s, a^4*((c.x s)^2+(c.y s)^2)^2≤2+δ) →
    Metric.closedBall (0:ℂ) (η/a) ⊆ convexHull ℝ ((fun s => (c.x s:ℂ)+(c.y s:ℂ)*Complex.I) '' Icc 0 L) :=
  expander_hull_disk_of_margin uniform_frame_gap

/-- Two time slices of any such homothetic solution share the dilation centre
    in their convex hulls, which excludes strict half-plane migration. -/
theorem no_migration_with_radius_gap : ∃ δ>0, ∀ (a L : ℝ), 0<a → 0<L →
    ∀ (c : ClosedExpander (a^4) L), (∀ s, a^4*((c.x s)^2+(c.y s)^2)^2≤2+δ) →
    let K := (fun s => (c.x s:ℂ)+(c.y s:ℂ)*Complex.I) '' Icc 0 L
    ∀ z w : ℂ, ¬ SimilarityHull.separated (SimilarityHull.directSimilarity 0 z '' K)
      (SimilarityHull.directSimilarity 0 w '' K) := by
  obtain ⟨δ,dp,η,ep,proved⟩ := uniform_expander_hull_disk
  refine ⟨δ,dp,?_⟩
  intro a L ap lp c cap K z w
  have origin : (0:ℂ) ∈ convexHull ℝ K := proved a L ap lp c cap
    (Metric.mem_closedBall_self (div_nonneg ep.le ap.le))
  exact SimilarityHull.not_separated_of_common_hull (SimilarityHull.center_mem_direct_hull origin z)
    (SimilarityHull.center_mem_direct_hull origin w)

end MigrationGeometry.HullGap
#print axioms MigrationGeometry.HullGap.uniform_expander_hull_disk

#print axioms MigrationGeometry.HullGap.no_migration_with_radius_gap
