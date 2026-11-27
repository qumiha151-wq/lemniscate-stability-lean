import Migration.BendingDissipation

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.ProjectedHeight

def weight (δ z : ℝ) := Real.sqrt (z^2+δ^2)
def first (δ z : ℝ) := z / weight δ z
def second (δ z : ℝ) := δ^2 / (weight δ z)^3
def bulk (δ z : ℝ) := z*(1+δ^2)/weight δ z
def tip (δ z : ℝ) := δ^2*(1+δ^2)/(weight δ z)^3

private theorem wp {δ : ℝ} (hd : 0<δ) (z : ℝ) : 0<weight δ z :=
  Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hd))
private theorem ws (δ z : ℝ) : weight δ z^2 = z^2+δ^2 := Real.sq_sqrt (by positivity)

theorem weight_derivative {δ : ℝ} (hd : 0<δ) (z : ℝ) :
    HasDerivAt (weight δ) (first δ z) z := by
  apply ((((hasDerivAt_id z).pow 2).add_const (δ^2)).sqrt (by change z^2+δ^2≠0; exact (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hd)).ne')).congr_deriv
  dsimp [first,weight]
  ring

theorem first_derivative {δ : ℝ} (hd : 0<δ) (z : ℝ) :
    HasDerivAt (first δ) (second δ z) z := by
  apply ((hasDerivAt_id z).div (weight_derivative hd z) (wp hd z).ne').congr_deriv
  dsimp only [id_eq,first,second]
  field_simp [(wp hd z).ne']
  nlinarith only [ws δ z]

private theorem factors {δ z w : ℝ} (hd : 0<δ) (unit : w^2+z^2=1) :
    z*weight δ z+w^2*first δ z=bulk δ z ∧
    weight δ z-z*first δ z+w^2*second δ z=tip δ z := by
  dsimp only [first,second,bulk,tip]
  have sq := ws δ z
  constructor
  · field_simp [(wp hd z).ne']
    linear_combination z*sq + z*unit
  · field_simp [(wp hd z).ne']
    linear_combination (weight δ z^2+δ^2)*sq+δ^2*unit

end ProjectedHeight
namespace SmoothPeriodicImmersion
open ProjectedHeight
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

private theorem projected_normal_rate (flow : c.IsNormalFEF) {t : ℝ} (ht : t∈I) (u : ℝ) :
    c.velocityGradientNormal t u = -arcDerivative (c.position t) (force (c.position t)) u := by
  let x := c.position t
  have reg := c.immersion t ht
  have smooth := c.position_slice_smooth ht
  have cf := force_smooth smooth reg
  have hv : c.velocity t = fun s => (-force x s) • normal x s := funext (c.velocity_eq_normal flow ht)
  have df := (cf.differentiable (by simp) u).hasDerivAt
  have dn : HasDerivAt (normal x) ((-(speed x u*curvature x u)) • tangent x u) u := by
    simpa only [Complex.real_smul,Complex.ofReal_neg] using normal_hasDerivAt smooth reg u
  have der := df.neg.smul dn
  change HasDerivAt (fun s => -force x s • normal x s)
    ((-force x u) • (-(speed x u*curvature x u)) • tangent x u +
      (-deriv (force x) u) • normal x u) u at der
  change inner ℝ (arcDerivative x (c.velocity t) u) (normal x u) = -arcDerivative x (force x) u
  rw [hv]
  simp only [arcDerivative,der.deriv,inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,
    normal_unit (γ:=x) reg,tangent_normal_orthogonal,smul_eq_mul]
  ring

def projectedHeightMoment (H : ℂ →L[ℝ] ℝ) (level δ t : ℝ) :=
  ∫ u in 0..c.period, (H (c.position t u)-level)*weight δ (H (normal (c.position t) u))*speed (c.position t) u

def projectedHeightRate (H : ℂ →L[ℝ] ℝ) (level δ t : ℝ) :=
  ∫ u in 0..c.period, force (c.position t) u *
    (-(bulk δ (H (normal (c.position t) u)))+
    (H (c.position t u)-level)*curvature (c.position t) u*tip δ (H (normal (c.position t) u)))*
    speed (c.position t) u

private def unreducedRate (H : ℂ →L[ℝ] ℝ) (level δ t u : ℝ) :=
  let x := c.position t
  let h := H (x u)-level
  let z := H (normal x u)
  let w := H (tangent x u)
  let F := force x u
  (-F*z*weight δ z - h*first δ z*w*c.velocityGradientNormal t u+
      h*curvature x u*F*weight δ z)*speed x u

private theorem moment_deriv_raw (flow : c.IsNormalFEF) (H : ℂ →L[ℝ] ℝ) (level : ℝ) {δ : ℝ}
    (hd : 0<δ) {t : ℝ} (ht : t∈I) : HasDerivAt (c.projectedHeightMoment H level δ)
      (∫ u in 0..c.period, c.unreducedRate H level δ t u) t := by
  have hh := (H.continuous.comp_continuousOn c.joint_smooth.continuousOn).sub
    (continuousOn_const (c := level))
  have zn := H.continuous.comp_continuousOn c.normal_joint_smooth.continuousOn
  have wt := H.continuous.comp_continuousOn c.tangent_joint_smooth.continuousOn
  have cw := continuous_iff_continuousAt.mpr fun z => (weight_derivative hd z).continuousAt
  have cf := continuous_iff_continuousAt.mpr fun z => (first_derivative hd z).continuousAt
  have sub : I ×ˢ uIcc 0 c.period ⊆ I ×ˢ (univ : Set ℝ) := fun z hz => ⟨hz.1, mem_univ _⟩
  apply hasDerivAt_intervalIntegral_of_continuousOn (a:=0) (b:=c.period)
    (F:=fun v u => (H (c.position v u)-level)*weight δ (H (normal (c.position v) u))*speed (c.position v) u)
    (D:=c.unreducedRate H level δ) c.time_open
  · exact ((hh.mul (cw.comp_continuousOn zn)).mul c.speed_joint_smooth.continuousOn).mono sub
  · have ff := c.force_joint_smooth.continuousOn
    have ck := c.curvature_joint_smooth.continuousOn
    exact (((((ff.neg.mul zn).mul (cw.comp_continuousOn zn)).sub
      (((hh.mul (cf.comp_continuousOn zn)).mul wt).mul c.velocityGradientNormal_joint_smooth.continuousOn)).add
      (((hh.mul ck).mul ff).mul (cw.comp_continuousOn zn))).mul c.speed_joint_smooth.continuousOn).mono sub
  · intro v hv u _
    have dH := (H.hasFDerivAt.comp_hasDerivAt v (flow v hv u)).sub_const level
    have n := c.normal_time_hasDerivAt hv u
    rw [← Complex.ofReal_neg,← Complex.real_smul] at n
    have dz := H.hasFDerivAt.comp_hasDerivAt v n
    apply ((dH.mul ((weight_derivative hd _).comp v dz)).mul
      (c.speed_normal_hasDerivAt flow hv u)).congr_deriv
    dsimp only [unreducedRate,Function.comp_apply,Pi.mul_apply]
    simp only [map_smul,smul_eq_mul]
    ring
  · exact ht

private theorem rate_reduction (flow : c.IsNormalFEF) (H : ℂ →L[ℝ] ℝ)
    (unit : ∀ Z : ℂ, (H Z)^2+(H (Complex.I*Z))^2=‖Z‖^2) (level : ℝ) {δ : ℝ}
    (hd : 0<δ) {t : ℝ} (ht : t∈I) :
    (∫ u in 0..c.period, c.unreducedRate H level δ t u)=c.projectedHeightRate H level δ t := by
  let x := c.position t
  let h := fun s => H (x s)-level
  let z := fun s => H (normal x s)
  let w := fun s => H (tangent x s)
  let g := speed x
  let k := curvature x
  let F := force x
  let Fs := arcDerivative x F
  let G := fun s => F s*(-bulk δ (z s)+h s*k s*tip δ (z s))*g s
  let U := fun s => h s*first δ (z s)*w s*F s
  have reg := c.immersion t ht
  have smooth := c.position_slice_smooth ht
  have hp := c.periodic t ht
  have ch : Continuous h := (H.continuous.comp smooth.continuous).sub continuous_const
  have cz : Continuous z := H.continuous.comp (normal_smooth smooth reg).continuous
  have cv : Continuous w := H.continuous.comp (tangent_smooth smooth reg).continuous
  have cg := (speed_smooth smooth reg).continuous
  have ck := (curvature_smooth smooth reg).continuous
  have cf := (force_smooth smooth reg).continuous
  have cfs := (arcDerivative_smooth smooth reg (force_smooth smooth reg)).continuous
  have cW := continuous_iff_continuousAt.mpr fun a => (weight_derivative hd a).continuousAt
  have cJ := continuous_iff_continuousAt.mpr fun a => (first_derivative hd a).continuousAt
  have cpow : Continuous (bulk δ) := (continuous_id.mul continuous_const).div cW (fun z => (wp hd z).ne')
  have ctip : Continuous (tip δ) := continuous_const.div (cW.pow 3) (fun z => pow_ne_zero _ (wp hd z).ne')
  have rawEq (s : ℝ) : c.unreducedRate H level δ t s=
      (-F s*z s*weight δ (z s)+h s*first δ (z s)*w s*Fs s+h s*k s*F s*weight δ (z s))*g s := by
    unfold unreducedRate
    rw [c.projected_normal_rate flow ht]
    dsimp only [x,h,z,w,F,Fs,k,g]
    ring
  have rawCont : Continuous (c.unreducedRate H level δ t) := by
    rw [funext rawEq]
    exact (((((cf.neg.mul cz).mul (cW.comp cz)).add (((ch.mul (cJ.comp cz)).mul cv).mul cfs)).add
      (((ch.mul ck).mul cf).mul (cW.comp cz))).mul cg)
  have endCont : Continuous G :=
    (cf.mul ((cpow.comp cz).neg.add ((ch.mul ck).mul (ctip.comp cz)))).mul cg
  have dU (s : ℝ) : HasDerivAt U (c.unreducedRate H level δ t s-G s) s := by
    have dx := H.hasFDerivAt.comp_hasDerivAt s (position_hasDerivAt smooth reg s)
    have nt := normal_hasDerivAt smooth reg s
    rw [← Complex.ofReal_neg,← Complex.real_smul] at nt
    have dz := H.hasFDerivAt.comp_hasDerivAt s nt
    have tt := tangent_hasDerivAt smooth reg s
    rw [← Complex.real_smul] at tt
    have dw := H.hasFDerivAt.comp_hasDerivAt s tt
    have df : HasDerivAt F (g s*Fs s) s := hasDerivAt_speed_smul_arcDerivative reg
      ((force_smooth smooth reg).differentiable (by simp)) s
    have eq : w s^2+z s^2=1 := by
      calc
        _ = ‖tangent x s‖^2 := unit (tangent x s)
        _ = 1 := by rw [tangent_unit (γ:=x) reg,one_pow]
    obtain ⟨fa,fb⟩ := factors hd eq
    apply ((((dx.sub_const level).mul ((first_derivative hd _).comp s dz)).mul dw).mul df).congr_deriv
    simp only [map_smul,smul_eq_mul,Function.comp_apply,Pi.mul_apply]
    rw [rawEq]
    dsimp only [G]
    rw [←fa,←fb]
    change ((g s*w s*first δ (z s)+h s*(second δ (z s)*(-(g s*k s)*w s)))*w s+
      h s*first δ (z s)*(g s*k s*z s))*F s+h s*first δ (z s)*w s*(g s*Fs s)=_
    ring
  have ends : U c.period=U 0 := by
    have xP := hp 0
    have tP := tangent_periodic smooth hp 0
    have nP := normal_periodic smooth hp 0
    have fP := force_periodic smooth reg hp 0
    simp only [zero_add] at xP tP nP fP
    dsimp only [U,h,z,w,F,x]
    rw [xP,tP,nP,fP]
  have ft := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=c.period)
    (fun s _ => dU s) ((rawCont.sub endCont).intervalIntegrable 0 c.period)
  rw [intervalIntegral.integral_sub (rawCont.intervalIntegrable ..) (endCont.intervalIntegrable ..),ends,sub_self] at ft
  exact sub_eq_zero.mp ft

/-- Exact time derivative of the regularized absolute projected-height
    moment on a genuine smooth closed free elastic flow. -/
theorem projectedHeight_evolution (flow : c.IsNormalFEF) (H : ℂ →L[ℝ] ℝ)
    (unit : ∀ Z : ℂ, (H Z)^2+(H (Complex.I*Z))^2=‖Z‖^2) (level : ℝ) {δ : ℝ}
    (hd : 0<δ) {t : ℝ} (ht : t∈I) :
    HasDerivAt (c.projectedHeightMoment H level δ) (c.projectedHeightRate H level δ t) t := by
  rw [← c.rate_reduction flow H unit level hd ht]
  exact c.moment_deriv_raw flow H level hd ht

end SmoothPeriodicImmersion
end MigrationGeometry.Flow
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.projectedHeight_evolution
