import Migration.LowDefectPhysicalDisk

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion

/-- Buzano's inequality for the continuous material fields and a nonnegative
density. Reflection in the force direction also handles zero dissipation. -/
theorem weighted_force_product {p q f w : ℝ→ℝ} {L : ℝ} (hl : 0≤L)
    (cp : Continuous p) (cq : Continuous q) (cf : Continuous f) (cw : Continuous w)
    (hw : ∀u,0≤w u) :
    2*|∫u in 0..L,p u*f u*w u| * |∫u in 0..L,q u*f u*w u| ≤
      (∫u in 0..L,f u^2*w u) *
        (Real.sqrt (∫u in 0..L,p u^2*w u)*Real.sqrt (∫u in 0..L,q u^2*w u)
          +|∫u in 0..L,p u*q u*w u|) := by
  let B := fun (a b : ℝ→ℝ)=>∫u in 0..L,a u*b u*w u
  have sym (a b : ℝ→ℝ) : B a b=B b a := by
    apply intervalIntegral.integral_congr
    intro u _; dsimp only; ring
  have sq (a : ℝ→ℝ) : B a a=∫u in 0..L,a u^2*w u := by simp [B,pow_two]
  have lin (a b v : ℝ→ℝ) (ca : Continuous a) (cb : Continuous b) (cv : Continuous v) (x y : ℝ) :
      B (fun u=>x*a u-y*b u) v=x*B a v-y*B b v := by
    have h :
      (fun u=>(x*a u-y*b u)*v u*w u)=(fun u=>x*(a u*v u*w u)-y*(b u*v u*w u)) := by funext u; ring
    dsimp [B]
    rw [h,intervalIntegral.integral_sub (f:=fun u=>x*(a u*v u*w u)) (g:=fun u=>y*(b u*v u*w u))
        ((((ca.mul cv).mul cw).const_mul x).intervalIntegrable ..)
        ((((cb.mul cv).mul cw).const_mul y).intervalIntegrable ..),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have cs (a b : ℝ→ℝ) (ca : Continuous a) (cb : Continuous b) :
      |B a b|≤Real.sqrt (B a a)*Real.sqrt (B b b) := by
    rw [sq,sq]
    apply (intervalIntegral.abs_integral_le_integral_abs hl).trans
    apply le_trans _ (weighted_abs_force hl ca cb cw hw)
    apply le_of_eq
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    rw [abs_mul,abs_mul,abs_of_nonneg (hw u)]
  let J := B f f
  let A := B p f
  let T := fun u=>2*A*f u-J*p u
  have cT : Continuous T := (cf.const_mul _).sub (cp.const_mul _)
  have jp : 0≤J := intervalIntegral.integral_nonneg_of_forall hl
    (fun u=>mul_nonneg (mul_self_nonneg (f u)) (hw u))
  have len : B T T=J^2*B p p := by
    rw [show B T T=2*A*B f T-J*B p T from lin f p T cf cp cT _ _,
      sym f T,sym p T,show B T f=2*A*B f f-J*B p f from lin f p f cf cp cf _ _,
      show B T p=2*A*B f p-J*B p p from lin f p p cf cp cp _ _,sym f p]
    dsimp only [A,J]
    ring
  have ip : B T q=2*A*B q f-J*B p q := by
    rw [show B T q=2*A*B f q-J*B p q from lin f p q cf cp cq _ _,sym f q]
  have hh := cs T q cT cq
  rw [len,Real.sqrt_mul (sq_nonneg J),Real.sqrt_sq jp,ip] at hh
  change 2*|A| * |B q f|≤_
  rw [← sq f,← sq p,← sq q]
  change _≤J*(Real.sqrt (B p p)*Real.sqrt (B q q)+|B p q|)
  calc 2*|A| * |B q f| = |(2*A*B q f-J*B p q)+J*B p q| := by
        rw [sub_add_cancel,abs_mul,abs_mul]; norm_num
    _ ≤ |2*A*B q f-J*B p q|+|J*B p q| := abs_add_le _ _
    _ ≤ (J*Real.sqrt (B p p))*Real.sqrt (B q q)+J*|B p q| := by
        rw [abs_mul,abs_of_nonneg jp]
        exact add_le_add_left hh _
    _ = _ := by ring

variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

def supportFluxCorrelation (H : ℂ →L[ℝ] ℝ) (t : ℝ) : ℝ :=
  ∫u in 0..c.period,
    inner ℝ (normal (c.position t) u) (c.position t u-c.arclengthCentroid t) *
      (curvature (c.position t) u*(H (c.position t u)-c.centroidHeight H t)+
       H (normal (c.position t) u))*speed (c.position t) u

/-- The same physical force appears in both the dilation virial and the first
moment derivative. Their product retains the support/centroid correlation. -/
theorem centroidRate_virial_product (H : ℂ →L[ℝ] ℝ) {t : ℝ} (ht : t∈I) :
    2*c.bending t*c.coreLength t*|c.centroidRate H t| ≤
      c.localDissipation H (fun _=>1) t*(Real.sqrt (c.centeredSupportMoment t)*
        Real.sqrt (c.centroidFluxMoment H t)+|c.supportFluxCorrelation H t|) := by
  let γ := c.position t
  let f := force γ
  let w := speed γ
  let p := fun u=>inner ℝ (normal γ u) (γ u-c.arclengthCentroid t)
  let q := fun u=>curvature γ u*(H (γ u)-c.centroidHeight H t)+H (normal γ u)
  have smooth := c.position_slice_smooth ht
  have reg := c.immersion t ht
  have cf := (force_smooth smooth reg).continuous
  have cw := (speed_smooth smooth reg).continuous
  have cp : Continuous p := (normal_smooth smooth reg).continuous.inner
    (smooth.continuous.sub continuous_const)
  have cq : Continuous q := ((curvature_smooth smooth reg).continuous.mul
    ((H.continuous.comp smooth.continuous).sub continuous_const)).add
      (H.continuous.comp (normal_smooth smooth reg).continuous)
  have h := weighted_force_product c.period_pos.le cp cq cf cw (fun u=>(speed_pos reg u).le)
  have vi := c.material_virial ht (c.arclengthCentroid t)
  have eq (u : ℝ) : p u*f u*w u=w u*f u*p u := by ring
  have a : |∫u in 0..c.period,p u*f u*w u|=c.bending t := by
    rw [funext eq,vi,abs_neg,abs_of_nonneg (c.bending_nonneg t)]
  have b : |∫u in 0..c.period,q u*f u*w u|=c.coreLength t*|c.centroidRate H t| := by
    change _=c.coreLength t*|(∫u in 0..c.period,q u*f u*w u)/c.coreLength t|
    rw [abs_div,abs_of_pos (c.coreLength_pos ht)]
    field_simp [(c.coreLength_pos ht).ne']
  have diss : (∫u in 0..c.period,f u^2*w u)=c.localDissipation H (fun _=>1) t := by
    simp [f,w,γ,localDissipation]
  change 2*|∫u in 0..c.period,p u*f u*w u| * |∫u in 0..c.period,q u*f u*w u|≤
    (∫u in 0..c.period,f u^2*w u)*(Real.sqrt (c.centeredSupportMoment t)*
    Real.sqrt (c.centroidFluxMoment H t)+|c.supportFluxCorrelation H t|) at h
  rw [a,b,diss] at h
  linarith only [h]

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.centroidRate_virial_product
