import Migration.MultiDiskFluxMoments
import Migration.MultiDiskConstants
import Migration.EscapingHulls
import Migration.DirectionalWidth

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- Integrate the two physical moments and the far-time support all the way
to the boundary of the resulting closed disk. -/
theorem multi_disk_of_snapshot_moments (hf : c.IsNormalFEF) {m s t : ℝ} (hm : 2≤m)
    (st : s≤t) (slab : Icc s t⊆I) (x : ℝ→ℝ)
    (xp : ∀v∈Icc s t, 0≤x v) (small : ∀v∈Icc s t,x v≤1/4)
    (prod : ∀v∈Icc s t, c.bending v*c.coreLength v=
      (2*Real.pi*m)*(Real.pi*m)*(1+(x v)^2*(1/m)^2))
    (mom : ∀e : ℂ, ‖e‖=1 → ∀v∈Icc s t,
      (2*Real.pi*m)*Real.sqrt (c.centeredSupportMoment v)≤c.coreLength v*Real.sqrt (c.coreLength v)*(1+x v) ∧
      Real.sqrt (c.centroidFluxMoment (innerSL ℝ e) v)≤Real.sqrt (c.coreLength v)*(x v*(1+(1+91/50*x v)/m)))
    (support : ∀e : ℂ, ‖e‖=1 → ∃u∈Icc 0 c.period,
      inner ℝ e (c.arclengthCentroid t)+c.coreLength t/(2*Real.pi*m)*(1-91/50*x t) ≤ inner ℝ e (c.position t u)) :
    Metric.closedBall (c.arclengthCentroid s)
      ((1+(1/m)^2/16)*((54/100)*(Real.pi*m)/c.bending s+(1/200)*(Real.pi*m)/c.bending t)) ⊆
        convexHull ℝ (c.position t '' Icc 0 c.period) := by
  let a:=2*Real.pi*m
  let U:=Real.pi*m
  let v:=1/m
  let C:=1+v^2/16
  let α:=54/100*C*U
  let β:=109/200*C*U
  let R:=C*((54/100)*U/c.bending s+(1/200)*U/c.bending t)
  have mp : 0<m := by linarith
  have ap : 0<a := by dsimp [a];positivity
  have up : 0<U := by dsimp [U];positivity
  have vp : 0≤v := by dsimp [v];positivity
  have ub : v≤1/2 := (div_le_iff₀ mp).mpr (by linarith)
  have hs : s∈Icc s t := ⟨le_rfl,st⟩
  have ht : t∈Icc s t := ⟨st,le_rfl⟩
  have pos r (hr : r∈Icc s t) : 0<c.bending r := c.bending_pos_of_width (slab hr)
  have Rp : 0<R := by dsimp [R,C];positivity [pos s hs,pos t ht]
  have eqR : R=α/c.bending s+(β-α)/c.bending t := by dsimp only [R,α,β];ring
  have budget (e : ℂ) (he : ‖e‖=1) (r) (hr : r∈Icc s t) :
      c.bending r*Real.sqrt (c.centroidFluxMoment (innerSL ℝ e) r)*Real.sqrt (c.centeredSupportMoment r)≤α*c.coreLength r := by
    let L:=c.coreLength r
    let E:=c.bending r
    let M:=c.centroidFluxMoment (innerSL ℝ e) r
    let J:=c.centeredSupportMoment r
    let q:=x r*(1+(1+91/50*x r)*v)
    let w:=1+x r
    have lp : 0<L := c.coreLength_pos (slab hr)
    have ep : 0<E := pos r hr
    obtain ⟨js,ms⟩:=mom e he r hr
    change a*Real.sqrt J≤L*Real.sqrt L*w at js
    change Real.sqrt M≤Real.sqrt L*(x r*(1+(1+91/50*x r)/m)) at ms
    have qeq : x r*(1+(1+91/50*x r)/m)=q := by dsimp only [q,v];ring
    rw [qeq] at ms
    have Mj:=mul_le_mul js ms (Real.sqrt_nonneg _) (by dsimp only [w];positivity [xp r hr])
    have both : a*(Real.sqrt M*Real.sqrt J)≤L^2*(w*q) := by
      rw [show a*(Real.sqrt M*Real.sqrt J)=(a*Real.sqrt J)*Real.sqrt M by ring]
      apply Mj.trans_eq
      rw [show L*Real.sqrt L*w*(Real.sqrt L*q)=L*(Real.sqrt L)^2*(w*q) by ring,Real.sq_sqrt lp.le];ring
    have hconst:=MigrationGeometry.MultiDisk.drift_constant (xp r hr) (small r hr) vp ub
    change (1+(x r)^2*v^2)*w*q≤54/100*C at hconst
    have scale:=mul_le_mul_of_nonneg_left hconst (show 0≤a*U*L by positivity)
    have elog : E*L=a*U*(1+(x r)^2*v^2) := prod r hr
    apply (mul_le_mul_iff_right₀ ap).mp
    change a*(E*Real.sqrt M*Real.sqrt J)≤a*(α*L)
    calc a*(E*Real.sqrt M*Real.sqrt J)=E*(a*(Real.sqrt M*Real.sqrt J)) := by ring
         _ ≤ E*(L^2*(w*q)) := mul_le_mul_of_nonneg_left both ep.le
         _ = (a*U*L)*((1+(x r)^2*v^2)*w*q) := by
           rw [show E*(L^2*(w*q))=(E*L)*L*(w*q) by ring,elog];ring
         _ ≤ (a*U*L)*(54/100*C) := scale
         _ = a*(α*L) := by dsimp only [α];ring
  have sup (e : ℂ) (he : ‖e‖=1) : ∃u∈Icc 0 c.period,
      inner ℝ e (c.arclengthCentroid t)+β/c.bending t ≤ inner ℝ e (c.position t u) := by
    obtain ⟨u,hu,b⟩:=support e he
    refine ⟨u,hu,le_trans (add_le_add_right ?_ _) b⟩
    apply (div_le_iff₀ (pos t ht)).mpr
    apply (mul_le_mul_iff_left₀ ap).mp
    have h:=MigrationGeometry.MultiDisk.support_constant (xp t ht) (small t ht) vp ub
    change 109/200*C≤(1+(x t)^2*v^2)*(1-91/50*x t) at h
    have hh:=mul_le_mul_of_nonneg_right h (mul_nonneg ap.le up.le)
    have eq:=prod t ht
    change c.bending t*c.coreLength t=a*U*(1+(x t)^2*v^2) at eq
    change β*a≤c.coreLength t/a*(1-91/50*x t)*c.bending t*a
    rw [show c.coreLength t/a*(1-91/50*x t)*c.bending t*a=(c.bending t*c.coreLength t)*(1-91/50*x t) by field_simp [ap.ne'],eq]
    dsimp only [β];linarith only [hh,show (109/200*C)*(a*U)=109/200*C*U*a by ring,
      show (1+(x t)^2*v^2)*(1-91/50*x t)*(a*U)=a*U*(1+(x t)^2*v^2)*(1-91/50*x t) by ring]
  let H:=convexHull ℝ (c.position t '' Icc 0 c.period)
  have closed : IsClosed H := (MigrationGeometry.SimilarityHull.compact_convexHull
    (isCompact_Icc.image (c.position_slice_smooth (slab ht)).continuous)).isClosed
  change Metric.closedBall (c.arclengthCentroid s) R⊆H
  rw [←closure_ball _ Rp.ne']
  apply closure_minimal _ closed
  intro z hz
  have gap := Metric.mem_ball.mp hz
  rw [eqR] at gap
  exact c.earlier_ball_of_spatial_flux_moments hf st slab pos budget sup gap (Metric.mem_closedBall.mpr le_rfl)

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.multi_disk_of_snapshot_moments

