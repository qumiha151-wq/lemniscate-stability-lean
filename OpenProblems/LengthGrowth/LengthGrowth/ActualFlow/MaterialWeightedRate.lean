import LengthGrowth.ActualFlow.WeightedEnergyVariation

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

private theorem normalFrameRate (hf : c.IsNormalFEF) {t : ℝ} (ht : t∈I) (u : ℝ) :
    c.velocityGradientNormal t u = -arcDerivative (c.position t) (force (c.position t)) u ∧
    c.velocityGradientTangent t u = curvature (c.position t) u*force (c.position t) u := by
  let x := c.position t
  have reg := c.immersion t ht
  have smooth := c.position_slice_smooth ht
  have cf := force_smooth smooth reg
  have hv : c.velocity t = fun s => (-force x s) • normal x s := by
    funext s
    simpa only [Complex.real_smul,Complex.ofReal_neg] using c.normal_velocity_eq hf ht s
  have df : HasDerivAt (force x) (deriv (force x) u) u := (cf.differentiable (by simp) u).hasDerivAt
  have dn : HasDerivAt (normal x) ((-(speed x u*curvature x u)) • tangent x u) u := by
    simpa only [Complex.real_smul,Complex.ofReal_neg] using normal_hasDerivAt smooth reg u
  have der := df.neg.smul dn
  change HasDerivAt (fun s => -force x s • normal x s)
    ((-force x u) • (-(speed x u*curvature x u)) • tangent x u +
      (-deriv (force x) u) • normal x u) u at der
  have ort := tangent_normal_orthogonal (γ:=x) u
  have rev : inner ℝ (normal x u) (tangent x u)=0 := by rw [real_inner_comm,ort]
  change inner ℝ (arcDerivative x (c.velocity t) u) (normal x u) = -arcDerivative x (force x) u ∧
    inner ℝ (arcDerivative x (c.velocity t) u) (tangent x u) = curvature x u*force x u
  rw [hv]
  simp only [arcDerivative,der.deriv,inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,
    normal_unit (γ:=x) reg,tangent_unit (γ:=x) reg,ort,rev,smul_eq_mul]
  constructor <;> field_simp [(speed_pos (γ:=x) reg u).ne'] <;> ring

/-- The exponential rate estimate itself on a smooth real material flow. -/
theorem material_exponential_rate (hf : c.IsNormalFEF) (l : ℂ →L[ℝ] ℝ) (hl : ∀z, |l z|≤‖z‖)
    (a M : ℝ) {t : ℝ} (ht : t∈I) (bound : ∀u∈Icc 0 c.period, |curvature (c.position t) u|≤M) :
    deriv (c.materialExponentialMass l a) t ≤ 256*(a^4+a^2*M^2)*c.materialExponentialMass l a t := by
  let x := c.position t
  let k := curvature x
  let j := curvatureGradient x
  let F := force x
  let g := speed x
  let p := arcDerivative x F
  let q := fun u => l (tangent x u)
  let n := fun u => l (normal x u)
  let w := fun u => Real.exp (a*l (x u))
  let dens := fun u => w u*(k u^2/2+a^2)*g u
  let time := fun u => w u*(-a*n u*F u*(k u^2/2+a^2)*g u+
    k u*deriv (c.velocityGradientNormal t) u+(a^2-k u^2/2)*(g u*c.velocityGradientTangent t u))
  let flux := fun u => -(w u*k u)*p u+(w u*(a*q u*k u+j u))*F u+8*a^2*w u*k u*j u
  have reg := c.immersion t ht
  have smooth := c.position_slice_smooth ht
  have per := c.periodic t ht
  have ck := curvature_smooth smooth reg
  have cj := curvatureGradient_smooth smooth reg
  have cF := force_smooth smooth reg
  have cp := arcDerivative_smooth smooth reg cF
  have cg := speed_smooth smooth reg
  have ct := tangent_smooth smooth reg
  have cn := normal_smooth smooth reg
  have cw : ContDiff ℝ ∞ w := (contDiff_const.mul (l.contDiff.comp smooth)).exp
  have cq : ContDiff ℝ ∞ q := l.contDiff.comp ct
  have cnn : ContDiff ℝ ∞ n := l.contDiff.comp cn
  have gN := joint_smooth_space_slice (f:=c.velocityGradientNormal) c.velocityGradientNormal_joint_smooth ht
  have gT := joint_smooth_space_slice (f:=c.velocityGradientTangent) c.velocityGradientTangent_joint_smooth ht
  have cdN := (contDiff_infty_iff_deriv.mp gN).2.continuous
  have ctime : Continuous time := by dsimp only [time]; fun_prop
  have cflux : ContDiff ℝ ∞ flux := by dsimp only [flux]; fun_prop
  have cdens : Continuous dens := by dsimp only [dens]; fun_prop
  have hdflux := (contDiff_infty_iff_deriv.mp cflux).2.continuous
  have ps := arcDerivative_periodic smooth per (cF.differentiable (by simp)) (force_periodic smooth reg per)
  have periodic : Function.Periodic flux c.period := by
    intro u
    simp only [flux,w,q,k,j,F,p,x,per u,tangent_periodic smooth per u,
      curvature_periodic smooth reg per u,curvatureGradient_periodic smooth reg per u,
      force_periodic smooth reg per u,ps u]
  have hfz := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=c.period)
    (fun u _ => (cflux.differentiable (by simp) u).hasDerivAt) (hdflux.intervalIntegrable _ _)
  have ep : flux c.period=flux 0 := by simpa only [zero_add] using periodic 0
  rw [ep,sub_self] at hfz
  have neqn : c.velocityGradientNormal t=fun u => -p u := funext (fun u => (c.normalFrameRate hf ht u).1)
  have est (u : ℝ) (hu : u∈Icc 0 c.period) :
      time u-deriv flux u ≤ 256*(a^4+a^2*M^2)*dens u := by
    have hk := curvature_hasDerivAt smooth reg u
    have hj := curvatureGradient_hasDerivAt smooth reg u
    have hp := cp.differentiable (by simp) u
    have hF : HasDerivAt F (g u*p u) u := hasDerivAt_speed_smul_arcDerivative reg (cF.differentiable (by simp)) u
    have hx : HasDerivAt (fun u => l (x u)) (g u*q u) u := by
      simpa only [Function.comp_def,map_smul,smul_eq_mul] using l.hasFDerivAt.comp_hasDerivAt u (position_hasDerivAt smooth reg u)
    have hq : HasDerivAt q (g u*k u*n u) u := by
      simpa only [q,g,k,n,Function.comp_def,←Complex.real_smul,map_smul,smul_eq_mul] using
        l.hasFDerivAt.comp_hasDerivAt u (tangent_hasDerivAt smooth reg u)
    have hw : HasDerivAt w (w u*(a*(g u*q u))) u := (hx.const_mul a).exp
    have hh := (((hw.mul hk).neg.mul hp.hasDerivAt).add
      ((hw.mul (((hq.const_mul a).mul hk).add hj)).mul hF)).add
        (((hw.const_mul (8*a^2)).mul hk).mul hj)
    have hfcut : F u-k u^3/2=curvatureSecond x u := by simp [F,k,force]
    have s1 := LengthGrowth.ClosedFrenetCurve.weighted_square_bound a (k u) (j u) (F u)
      (q u) (n u) ((hl _).trans_eq (tangent_unit reg u)) ((hl _).trans_eq (normal_unit reg u))
    rw [hfcut] at s1
    have ks : k u^2≤M^2 := sq_le_sq' (abs_le.mp (bound u hu)).1 (abs_le.mp (bound u hu)).2
    have cv : a^4+a^2*k u^2≤a^4+a^2*M^2 := by gcongr
    have cv' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left cv (by norm_num : (0:ℝ)≤256)) (show 0≤k u^2/2+a^2 by positivity)
    have G := mul_le_mul_of_nonneg_left (s1.trans cv') (mul_nonneg (show 0≤w u from (Real.exp_pos _).le) (speed_pos reg u).le)
    have dNeq : deriv (c.velocityGradientNormal t) u= -deriv p u := by
      rw [neqn]; exact hp.hasDerivAt.neg.deriv
    have dTeq := (c.normalFrameRate hf ht u).2
    dsimp only [time,dens]
    rw [dNeq,dTeq,show deriv flux u=_ from hh.deriv]
    dsimp only [LengthGrowth.ClosedFrenetCurve.weightedRateIntegrand,k,j,F,p,g,w,q,n,x,force,
      Pi.add_apply,Pi.mul_apply,Pi.neg_apply] at G ⊢
    linarith only [G]
  have ci := intervalIntegral.integral_mono_on (μ:=volume) c.period_pos.le
    ((ctime.sub hdflux).intervalIntegrable _ _) ((cdens.const_mul (256*(a^4+a^2*M^2))).intervalIntegrable _ _) est
  simp only [Pi.sub_apply] at ci
  rw [intervalIntegral.integral_sub (ctime.intervalIntegrable _ _) (hdflux.intervalIntegrable _ _),
    hfz,sub_zero,intervalIntegral.integral_const_mul] at ci
  rw [(c.materialExponentialMass_hasDerivAt hf l a ht).deriv]
  exact ci

/-- The same material moment detects each original label at arbitrary speed. -/
theorem material_exponential_detection {t : ℝ} (ht : t∈I) (l : ℂ →L[ℝ] ℝ)
    (hl : ∀z, |l z|≤‖z‖) {a m : ℝ} (ha : 0≤a) (hm : 0≤m) (hL : m≤c.length t)
    (u : ℝ) : m*a^2*Real.exp (a*(l (c.position t u)-m))≤c.materialExponentialMass l a t := by
  let p := c.regularPositionAt ht
  let f := fun u => Real.exp (a*l (p.position u))*(curvature p.position u^2/2+a^2)
  have cf : Continuous f := ((l.continuous.comp p.smooth.continuous).const_mul a).rexp.mul
    ((((curvature_smooth p.smooth p.regular).continuous.pow 2).div_const 2).add continuous_const)
  have detection := p.closedFrenetCurve.exponentialMass_detects_position l hl ha hm hL (p.arclength u)
  have coord (z : ℝ) : p.closedFrenetCurve.curve z=p.position (p.arclengthInverse z) := rfl
  unfold LengthGrowth.ClosedFrenetCurve.exponentialMass at detection
  simp_rw [coord,p.closedFrenetCurve_curvature,p.closedFrenetCurve_period] at detection
  rw [p.arclength_inverse_right] at detection
  change _ ≤ ∫ s in 0..p.length, f (p.arclengthInverse s) at detection
  rw [p.integral_comp_inverse cf] at detection
  exact detection

end LengthGrowth.ActualFlow.SmoothPeriodicImmersion
#print axioms LengthGrowth.ActualFlow.SmoothPeriodicImmersion.material_exponential_rate
#print axioms LengthGrowth.ActualFlow.SmoothPeriodicImmersion.material_exponential_detection
