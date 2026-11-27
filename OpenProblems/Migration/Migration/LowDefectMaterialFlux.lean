import Migration.LowDefectFluxNorm
import Migration.LowDefectPhysicalDisk
import Migration.LowDefectMaterialSupport

noncomputable section
open Set MeasureTheory
namespace MigrationGeometry.Flow.PeriodicRegularPosition
variable (p : PeriodicRegularPosition)

theorem fractional_integral_eq {f : ℝ→ℝ} (cf : Continuous f) :
    p.length*(∫x in (0:ℝ)..1,f (p.arclengthInverse (p.length*x)))=
      ∫u in 0..p.period,f u*speed p.position u := by
  let g := fun s => f (p.arclengthInverse s)
  change p.length*(∫x in (0:ℝ)..1,g (p.length*x))=_
  rw [intervalIntegral.integral_comp_mul_left g p.length_pos.ne',mul_zero,mul_one,smul_eq_mul,←mul_assoc,mul_inv_cancel₀ p.length_pos.ne',one_mul]
  exact p.integral_comp_inverse cf

end MigrationGeometry.Flow.PeriodicRegularPosition
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem actual_directional_flux_bound {t : ℝ} (ht : t∈I)
    (turn : c.signedCurvatureIntegral t=2*Real.pi)
    (small : c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2≤14/100)
    (e : ℂ) (he : ‖e‖=1) :
    let D := c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2
    let x := Real.sqrt D
    Real.sqrt (c.centroidFluxMoment (innerSL ℝ e) t) ≤
      x*(1750/1000+575/1000*x+133/1000*x^2)*Real.sqrt (c.coreLength t) := by
  let p := c.materialSlice ht
  let a := 2*Real.pi
  let D := c.curvatureOscillation a t/a^2
  let H := 575/1000*Real.sqrt D+133/1000*D
  let M := 1+H
  let B := c.arclengthCentroid t
  let G := p.fractionalPosition B
  let T := p.fractionalTangent
  let K := fun s=> (p.fractionalCurvature s-a)/a
  let Z := fun s=>G s+Complex.I*T s
  have ap : 0<a := by dsimp [a]; positivity
  have Dp : 0≤D := div_nonneg (c.curvatureOscillation_nonneg ht _) (sq_nonneg _)
  have Mp : 0≤M := by dsimp [M,H]; positivity
  have rawK : Continuous p.fractionalCurvature := continuous_const.mul
    ((curvature_smooth p.smooth p.regular).continuous.comp
      (p.inverse_continuous.comp (continuous_const.mul continuous_id)))
  have ck : Continuous K := (rawK.sub continuous_const).div_const a
  have cg : Continuous G := continuous_iff_continuousAt.mpr fun s=>(p.fractionalPosition_der B s).continuousAt
  have ct : Continuous T := continuous_iff_continuousAt.mpr fun s=>(p.fractionalTangent_hasDerivAt s).continuousAt
  have cz : Continuous Z := cg.add (continuous_const.mul ct)
  have moment : (∫s in (0:ℝ)..1,K s^2)=D := by
    dsimp only [K,D]
    simp_rw [div_pow]
    rw [intervalIntegral.integral_div,p.fractionalCurvature_oscillation]
    rfl
  have upper := (c.material_normalized_support ht turn small).1
  have normFlux := LowDefect.flux_norm_sq ck cg cz Mp upper moment (c.material_normal_correction ht turn small)
  let u := fun s=>p.arclengthInverse (p.length*s)
  let Q := fun v=>curvature p.position v*(inner ℝ e (p.position v)-c.centroidHeight (innerSL ℝ e) t)+inner ℝ e (normal p.position v)
  have cq : Continuous Q := ((curvature_smooth p.smooth p.regular).continuous.mul
    (((innerSL ℝ e).continuous.comp p.smooth.continuous).sub continuous_const)).add
      ((innerSL ℝ e).continuous.comp (normal_smooth p.smooth p.regular).continuous)
  have xy (s : ℝ) : K s • G s+Z s=
      curvature p.position (u s) • (p.position (u s)-B)+normal p.position (u s) := by
    change ((p.length*curvature p.position (u s)-a)/a) • ((a/p.length) • (p.position (u s)-B))+
      ((a/p.length) • (p.position (u s)-B)+Complex.I*tangent p.position (u s))=_
    rw [normal,←add_assoc,smul_smul,←add_smul]
    have E : (p.length*curvature p.position (u s)-a)/a*(a/p.length)+a/p.length=curvature p.position (u s) := by
      field_simp [ap.ne',p.length_pos.ne'];ring
    rw [E]
  have proj (s : ℝ) : Q (u s)=inner ℝ e (K s • G s+Z s) := by
    rw [xy,inner_add_right,real_inner_smul_right,inner_sub_right]
    change _=_*(_-((innerSL ℝ e) B))+_
    rw [show ((innerSL ℝ e) B)=c.centroidHeight (innerSL ℝ e) t from c.map_arclengthCentroid _ ht]
  have estimate (s : ℝ) : Q (u s)^2≤‖K s • G s+Z s‖^2 := by
    have h := abs_real_inner_le_norm e (K s • G s+Z s)
    rw [he,one_mul,←proj] at h
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
  have cu : Continuous u := p.inverse_continuous.comp (continuous_const.mul continuous_id)
  have b := intervalIntegral.integral_mono_on (μ:=volume) (by norm_num : (0:ℝ)≤1)
    (((cq.comp cu).pow 2).intervalIntegrable ..) ((((ck.smul cg).add cz).norm.pow 2).intervalIntegrable ..)
    (fun s _=>estimate s)
  have convertMoment := p.fractional_integral_eq (cq.pow 2)
  change p.length*(∫s in (0:ℝ)..1,Q (u s)^2)=c.centroidFluxMoment (innerSL ℝ e) t at convertMoment
  have scaled := mul_le_mul_of_nonneg_left (b.trans normFlux) p.length_pos.le
  change p.length*(∫s in (0:ℝ)..1,Q (u s)^2) ≤ p.length*((M+75/100)^2*D) at scaled
  rw [convertMoment] at scaled
  have L : p.length=c.coreLength t := rfl
  rw [L] at scaled
  change Real.sqrt _≤Real.sqrt D*_*Real.sqrt (c.coreLength t)
  rw [Real.sq_sqrt Dp]
  have mp : 0≤1750/1000+575/1000*Real.sqrt D+133/1000*D := by positivity
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · rw [mul_pow,mul_pow,Real.sq_sqrt Dp,Real.sq_sqrt (c.coreLength_pos ht).le]
    dsimp only [M,H] at scaled
    linarith only [scaled]

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.actual_directional_flux_bound
