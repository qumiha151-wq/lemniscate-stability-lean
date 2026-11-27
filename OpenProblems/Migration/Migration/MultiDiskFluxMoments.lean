import Migration.LowDefectMaterialFlux

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow

/-- An L² triangle estimate for two continuous majorants on normalized arclength. -/
theorem sum_majorant_moment {f g y : ℝ→ℝ} {A B : ℝ} (cf : Continuous f) (cg : Continuous g)
    (cy : Continuous y) (ap : 0≤A) (bp : 0≤B)
    (fm : (∫x in (0:ℝ)..1,f x^2)≤A^2) (gm : (∫x in (0:ℝ)..1,g x^2)≤B^2)
    (point : ∀x∈Icc (0:ℝ) 1, |y x|≤f x+g x) :
    (∫x in (0:ℝ)..1,y x^2)≤(A+B)^2 := by
  have zr : (0:ℝ)≤1 := by norm_num
  have b:=intervalIntegral.integral_mono_on (μ:=volume) zr ((cy.pow 2).intervalIntegrable ..)
    (((cf.add cg).pow 2).intervalIntegrable ..)
    (fun x hx=>show y x^2≤(f x+g x)^2 by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (y x)) (point x hx) 2)
  change (∫x in (0:ℝ)..1,y x^2)≤_ at b
  apply b.trans
  change (∫x in (0:ℝ)..1,(f x+g x)^2)≤_
  have eq (x : ℝ) : (f x+g x)^2=f x^2+g x^2+2*(f x*g x) := by ring
  simp only [eq]
  rw [intervalIntegral.integral_add (f:=fun x=>f x^2+g x^2) (g:=fun x=>2*(f x*g x))
    (((cf.pow 2).add (cg.pow 2)).intervalIntegrable ..) ((continuous_const.mul (cf.mul cg)).intervalIntegrable ..),
    intervalIntegral.integral_add (f:=fun x=>f x^2) (g:=fun x=>g x^2) ((cf.pow 2).intervalIntegrable ..) ((cg.pow 2).intervalIntegrable ..),
    intervalIntegral.integral_const_mul]
  have cs:=interval_integral_abs_mul_le cf cg zr
  have mono:=intervalIntegral.integral_mono_on (μ:=volume) zr ((cf.mul cg).intervalIntegrable ..) ((cf.mul cg).abs.intervalIntegrable ..)
    (fun x _=>le_abs_self (f x*g x))
  have csm:=mul_le_mul ((Real.sqrt_le_sqrt fm).trans_eq (Real.sqrt_sq ap))
    ((Real.sqrt_le_sqrt gm).trans_eq (Real.sqrt_sq bp)) (Real.sqrt_nonneg _) ap
  change (∫x in (0:ℝ)..1,f x*g x)≤_ at mono
  nlinarith only [mono.trans (cs.trans csm),fm,gm]

end MigrationGeometry.Flow
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- Convert the position and normal correction bounds into both physical virial moments. -/
theorem multi_material_flux_moments {t m x : ℝ} (ht : t∈I) (mp : 0<m) (xp : 0≤x)
    (defect : c.curvatureOscillation (2*Real.pi*m) t=(2*Real.pi)^2*x^2)
    (correction : (∫s in (0:ℝ)..1,‖m • (c.materialSlice ht).fractionalPosition (c.arclengthCentroid t) s+
        Complex.I*(c.materialSlice ht).fractionalTangent s‖^2)≤x^2)
    (outer : ∀s∈Icc (0:ℝ) 1, ‖m • (c.materialSlice ht).fractionalPosition (c.arclengthCentroid t) s‖≤1+91/50*x)
    (e : ℂ) (he : ‖e‖=1) :
    let L:=c.coreLength t
    (2*Real.pi*m)*Real.sqrt (c.centeredSupportMoment t)≤L*Real.sqrt L*(1+x) ∧
    Real.sqrt (c.centroidFluxMoment (innerSL ℝ e) t)≤Real.sqrt L*(x*(1+(1+91/50*x)/m)) := by
  let p:=c.materialSlice ht
  let B:=c.arclengthCentroid t
  let a:=2*Real.pi*m
  let G:=fun s=>m • p.fractionalPosition B s
  let T:=p.fractionalTangent
  let N:=fun s=>Complex.I*T s
  let Z:=fun s=>G s+N s
  let K:=fun s=>(p.fractionalCurvature s-a)/a
  let M:=1+91/50*x
  let u:=fun s=>p.arclengthInverse (p.length*s)
  let physicalP:=fun y=>inner ℝ (normal p.position y) (p.position y-B)
  let physicalQ:=fun y=>curvature p.position y*(inner ℝ e (p.position y)-c.centroidHeight (innerSL ℝ e) t)+inner ℝ e (normal p.position y)
  have ap : 0<a := by dsimp [a];positivity
  have lp:=p.length_pos
  have Mp : 0≤M := by dsimp [M];positivity
  have cg : Continuous G := (continuous_iff_continuousAt.mpr fun s=>(p.fractionalPosition_der B s).continuousAt).const_smul m
  have ct : Continuous T := continuous_iff_continuousAt.mpr fun s=>(p.fractionalTangent_hasDerivAt s).continuousAt
  have cn : Continuous N := continuous_const.mul ct
  have cz : Continuous Z := cg.add cn
  have ck : Continuous K := ((continuous_const.mul ((curvature_smooth p.smooth p.regular).continuous.comp
    (p.inverse_continuous.comp (continuous_const.mul continuous_id)))).sub continuous_const).div_const a
  have cp : Continuous physicalP := (normal_smooth p.smooth p.regular).continuous.inner (p.smooth.continuous.sub continuous_const)
  have cq : Continuous physicalQ := ((curvature_smooth p.smooth p.regular).continuous.mul
    (((innerSL ℝ e).continuous.comp p.smooth.continuous).sub continuous_const)).add
    ((innerSL ℝ e).continuous.comp (normal_smooth p.smooth p.regular).continuous)
  have cu : Continuous u:=p.inverse_continuous.comp (continuous_const.mul continuous_id)
  have gEq (s : ℝ) : G s=(a/p.length) • (p.position (u s)-B) := by
    change m • ((2*Real.pi/p.length) • (p.position (u s)-B))=_
    rw [smul_smul,show m*(2*Real.pi/p.length)=a/p.length by dsimp only [a];ring]
  have knorm : (∫s in (0:ℝ)..1,K s^2)=(x/m)^2 := by
    dsimp only [K];simp_rw [div_pow];rw [intervalIntegral.integral_div,p.fractionalCurvature_oscillation]
    change c.curvatureOscillation a t/a^2=_
    rw [defect];dsimp only [a];field_simp [Real.pi_ne_zero,mp.ne']
  have zMass : (∫s in (0:ℝ)..1,‖Z s‖^2)≤x^2 := correction
  have multK : (∫s in (0:ℝ)..1,(M*|K s|)^2)=(M*(x/m))^2 := by
    simp_rw [mul_pow,sq_abs];rw [intervalIntegral.integral_const_mul,knorm]
  have pMass : (∫s in (0:ℝ)..1,((a/p.length)*physicalP (u s))^2)≤(1+x)^2 := by
    apply sum_majorant_moment (f:=fun _=>1) (g:=fun s=>‖Z s‖) continuous_const cz.norm
      (continuous_const.mul (cp.comp cu)) (by norm_num) xp (by norm_num) zMass
    intro s _
    have nunit : ‖N s‖=1 := by change ‖normal p.position (u s)‖=1;exact normal_unit p.regular _
    have innerZ:=abs_real_inner_le_norm (N s) (Z s)
    rw [nunit,one_mul] at innerZ
    have id : (a/p.length)*physicalP (u s)=inner ℝ (N s) (Z s)-1 := by
      dsimp only [Z];rw [inner_add_right,real_inner_self_eq_norm_sq,nunit,one_pow,gEq,real_inner_smul_right,add_sub_cancel_right];rfl
    change |(a/p.length)*physicalP (u s)|≤1+‖Z s‖
    rw [id]
    exact (abs_sub _ _).trans (by simpa only [abs_one,add_comm] using add_le_add_right innerZ 1)
  have fMass : (∫s in (0:ℝ)..1,physicalQ (u s)^2)≤(x+M*(x/m))^2 := by
    apply sum_majorant_moment (f:=fun s=>‖Z s‖) (g:=fun s=>M*|K s|) cz.norm (continuous_const.mul ck.abs)
      (cq.comp cu) xp (mul_nonneg Mp (div_nonneg xp mp.le)) zMass multK.le
    intro s hs
    have phys : K s • G s+Z s=curvature p.position (u s) • (p.position (u s)-B)+normal p.position (u s) := by
      change K s • G s+(G s+N s)=_
      rw [←add_assoc,gEq,smul_smul,←add_smul]
      have eq : K s*(a/p.length)+a/p.length=curvature p.position (u s) := by
        change (p.length*curvature p.position (u s)-a)/a*(a/p.length)+a/p.length=_
        field_simp [ap.ne',lp.ne'];ring
      rw [eq];rfl
    have qeq : physicalQ (u s)=inner ℝ e (K s • G s+Z s) := by
      rw [phys,inner_add_right,real_inner_smul_right,inner_sub_right]
      rw [show inner ℝ e B=c.centroidHeight (innerSL ℝ e) t from c.map_arclengthCentroid (innerSL ℝ e) ht]
    change |physicalQ (u s)|≤‖Z s‖+M*|K s|
    rw [qeq]
    have cs:=abs_real_inner_le_norm e (K s • G s+Z s)
    rw [he,one_mul] at cs
    apply cs.trans ((norm_add_le _ _).trans ?_)
    rw [norm_smul,Real.norm_eq_abs]
    have O : ‖G s‖≤M := outer s hs
    linarith only [mul_le_mul_of_nonneg_left O (abs_nonneg (K s)),show |K s| *M=M*|K s| by ring]
  have pc:=p.fractional_integral_eq (cp.pow 2)
  have qc:=p.fractional_integral_eq (cq.pow 2)
  change p.length*(∫s in (0:ℝ)..1,physicalP (u s)^2)=c.centeredSupportMoment t at pc
  change p.length*(∫s in (0:ℝ)..1,physicalQ (u s)^2)=c.centroidFluxMoment (innerSL ℝ e) t at qc
  simp_rw [mul_pow] at pMass
  rw [intervalIntegral.integral_const_mul] at pMass
  have Pscale:=mul_le_mul_of_nonneg_left pMass (show 0≤p.length^3 by positivity)
  have Fscale:=mul_le_mul_of_nonneg_left fMass lp.le
  rw [qc] at Fscale
  have Pcancel : p.length^3*((a/p.length)^2*(∫s in (0:ℝ)..1,physicalP (u s)^2))=
      a^2*c.centeredSupportMoment t := by rw [←pc];field_simp
  rw [Pcancel] at Pscale
  change a*Real.sqrt (c.centeredSupportMoment t)≤p.length*Real.sqrt p.length*(1+x) ∧
    Real.sqrt (c.centroidFluxMoment (innerSL ℝ e) t)≤Real.sqrt p.length*(x*(1+M/m))
  constructor
  · apply le_of_sq_le_sq _ (by positivity)
    have jnon : 0≤c.centeredSupportMoment t := intervalIntegral.integral_nonneg_of_forall c.period_pos.le
      (fun u=>mul_nonneg (sq_nonneg _) (speed_pos (c.immersion t ht) u).le)
    rw [mul_pow a,Real.sq_sqrt jnon]
    rw [mul_pow (p.length*Real.sqrt p.length),mul_pow p.length,Real.sq_sqrt lp.le]
    nlinarith only [Pscale]
  · apply (Real.sqrt_le_iff).mpr ⟨by positivity,?_⟩
    rw [mul_pow (Real.sqrt p.length),Real.sq_sqrt lp.le]
    rw [show x*(1+M/m)=x+M*(x/m) by ring];exact Fscale

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.multi_material_flux_moments

