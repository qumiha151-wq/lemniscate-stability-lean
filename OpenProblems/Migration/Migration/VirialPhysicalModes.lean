import Migration.VirialModeConstants
import Migration.LowDefectMaterialSlab

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace MigrationGeometry.Flow.LowDefect

/-- Centroid flux in fractional arclength. The quadratic inequality keeps
the sharp sum of the two L² bounds, including the case D=0. -/
theorem quarter_flux_norm_sq {K : ℝ→ℝ} {G Z : ℝ→ℂ} (ck : Continuous K)
    (cg : Continuous G) (cz : Continuous Z) {M D : ℝ} (mp : 0≤M)
    (bound : ∀x∈Icc (0:ℝ) 1, ‖G x‖≤M)
    (kv : (∫x in (0:ℝ)..1,K x^2)=D)
    (zv : (∫x in (0:ℝ)..1,‖Z x‖^2)≤(755/1000)^2*D) :
    (∫x in (0:ℝ)..1,‖K x • G x+Z x‖^2) ≤ (M+755/1000)^2*D := by
  let f := fun x => ‖K x • G x+Z x‖^2
  let g := fun x => (M+755/1000)*(M*K x^2+(1000/755)*‖Z x‖^2)
  have cf : Continuous f := (((ck.smul cg).add cz).norm.pow 2)
  have cm : Continuous g := continuous_const.mul ((continuous_const.mul (ck.pow 2)).add (continuous_const.mul (cz.norm.pow 2)))
  have le (x : ℝ) (hx : x∈Icc (0:ℝ) 1) : f x≤g x := by
    have a := norm_add_le (K x • G x) (Z x)
    rw [norm_smul,Real.norm_eq_abs] at a
    have b := mul_le_mul_of_nonneg_left (bound x hx) (abs_nonneg (K x))
    have q := pow_le_pow_left₀ (norm_nonneg _) (a.trans (add_le_add b le_rfl)) 2
    change ‖K x • G x+Z x‖^2 ≤ (M+755/1000)*(M*K x^2+(1000/755)*‖Z x‖^2)
    have eq : K x^2=|K x|^2 := (sq_abs _).symm
    rw [eq]
    nlinarith only [q,mul_nonneg mp (sq_nonneg ((755/1000)*|K x|-‖Z x‖))]
  have scalar := intervalIntegral.integral_mono_on (μ:=volume) (by norm_num : (0:ℝ)≤1)
    (cf.intervalIntegrable ..) (cm.intervalIntegrable ..) le
  change (∫x in (0:ℝ)..1,f x) ≤ _
  apply scalar.trans
  dsimp only [g]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add (f:=fun x=>M*K x^2) (g:=fun x=>(1000/755)*‖Z x‖^2)
      ((continuous_const.mul (ck.pow 2)).intervalIntegrable ..)
      ((continuous_const.mul (cz.norm.pow 2)).intervalIntegrable ..),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,kv]
  have bz := mul_le_mul_of_nonneg_left zv (by linarith : 0≤(M+755/1000)*(1000/755))
  linarith

end MigrationGeometry.Flow.LowDefect

namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem quarter_second_harmonic_bounds {t : ℝ} (ht : t ∈ I)
    (turn : c.signedCurvatureIntegral t=2*Real.pi)
    (small : c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2 ≤ 1/4) :
    let T := (c.materialSlice ht).fractionalTangent
    let D := c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2
    1-LowDefect.Tangent.energy T 1 ≤ (27/100)*D ∧
      ‖LowDefect.Tangent.coeff T 2‖ ≤ (28/100)*D := by
  let p := c.materialSlice ht
  let T := p.fractionalTangent
  let D := c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2
  let m := LowDefect.Tangent.energy T
  have hm (n : ℤ) : 0 ≤ m n := sq_nonneg _
  have tc : Continuous T := continuous_iff_continuousAt.mpr
    fun x=>(p.fractionalTangent_hasDerivAt x).continuousAt
  have id := c.material_tangent_fourier_data ht turn
  obtain ⟨h0,ha,hn,hd⟩ := id
  have zero : m 0=0 := by
    change ‖LowDefect.Tangent.coeff (c.materialSlice ht).fractionalTangent 0‖^2=0
    rw [h0];norm_num
  have wm := LowDefect.leakage_from_moments hm zero ha hn hd
  have uc := LowDefect.Tangent.coefficient_leakage tc
    (fun x=>tangent_unit p.regular _) p.fractionalTangent_mean
  have uc2 := pow_le_pow_left₀ (by positivity) uc 2
  have zz : ‖LowDefect.Tangent.coeff T 2‖^2*(1-(1-m 1))≤(1-m 1)^2 := by
    change _≤(1-‖LowDefect.Tangent.coeff T 1‖^2)^2
    simpa [m,LowDefect.Tangent.energy,mul_pow] using uc2
  have dp : 0 ≤ D := div_nonneg (c.curvatureOscillation_nonneg ht _) (sq_nonneg _)
  exact LowDefect.quarter_mass_bootstrap dp small wm.1 zz wm.2.1 wm.2.2

end MigrationGeometry.Flow.SmoothPeriodicImmersion

namespace MigrationGeometry.Flow.LowDefect.Tangent

theorem quarter_position_harmonic_error {G T : ℝ→ℂ} {D : ℝ} (ct : Continuous T)
    (dg : ∀x,HasDerivAt G ((2*Real.pi:ℂ)*T x) x)
    (per : G 1=G 0) (zero : coeff G 0=0)
    (hd : HasSum (fun n : ℤ => ((n:ℝ)-1)^2*energy T n) D)
    (small : ‖coeff T 2‖≤(28/100)*D) {x : ℝ} (hx : x∈Ico 0 1) :
    ‖G x-coeff G 1*fourier 1 (x : AddCircle (1:ℝ))‖≤
      (575/1000)*Real.sqrt D+(140/1000)*D := by
  have cg : Continuous G := continuous_iff_continuousAt.mpr fun s=>(dg s).continuousAt
  obtain ⟨tail,bt⟩ := far_position_bound ct dg per hd
  have v2 : ‖coeff G 2‖≤(140/1000)*D := by
    rw [position_coefficient ct dg per (by decide : (2:ℤ)≠0)]
    norm_num [norm_mul,norm_div]
    linarith
  let e := fun n : ℤ=>fourier n (x : AddCircle (1:ℝ))
  have en (n : ℤ) : ‖e n‖=1 := Circle.norm_coe _
  let r := fun n : ℤ=>if n=1 then (0:ℂ) else coeff G n*e n
  have s2 : HasSum (fun n : ℤ=>if n=2 then ‖coeff G 2‖ else 0) ‖coeff G 2‖ := by
    simpa [eq_comm] using hasSum_ite_eq (2:ℤ) ‖coeff G 2‖
  have eq (n : ℤ) : ‖r n‖=farSize G n+(if n=2 then ‖coeff G 2‖ else 0) := by
    by_cases h0 : n=0
    · simp [r,farSize,h0,zero]
    by_cases h1 : n=1
    · simp [r,farSize,h1]
    by_cases h2 : n=2
    · simp [r,farSize,h2,en]
    simp [r,farSize,h0,h1,h2,en]
  have normsum : HasSum (fun n=>‖r n‖) ((∑'n,farSize G n)+‖coeff G 2‖) := by
    simpa only [eq] using tail.hasSum.add s2
  have s1 : HasSum (fun n : ℤ=>if n=1 then ‖coeff G 1‖ else 0) ‖coeff G 1‖ := by
    simpa [eq_comm] using hasSum_ite_eq (1:ℤ) ‖coeff G 1‖
  have normcoeff : Summable (fun n=>‖coeff G n‖) := by
    apply (normsum.summable.add s1.summable).congr
    intro n
    by_cases h : n=1 <;> simp [r,h,en]
  have recovery := fourier_recovery cg per normcoeff.of_norm hx
  have z : HasSum (fun n : ℤ=>if n=1 then coeff G 1*e 1 else 0) (coeff G 1*e 1) := by
    simpa [eq_comm] using hasSum_ite_eq (1:ℤ) (coeff G 1*e 1)
  have sum : HasSum r (G x-coeff G 1*e 1) := by
    apply (recovery.sub z).congr_fun
    intro n
    change (if n=1 then 0 else coeff G n*e n)=coeff G n*e n-(if n=1 then coeff G 1*e 1 else 0)
    by_cases h : n=1 <;> simp only [h,if_true,if_false,sub_self,sub_zero]
  have b := norm_tsum_le_tsum_norm normsum.summable
  rw [sum.tsum_eq,normsum.tsum_eq] at b
  exact b.trans (by linarith)

end MigrationGeometry.Flow.LowDefect.Tangent

namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem quarter_material_normal_correction {t : ℝ} (ht : t ∈ I)
    (turn : c.signedCurvatureIntegral t=2*Real.pi)
    (small : c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2 ≤ 1/4) :
    let p := c.materialSlice ht
    let G := p.fractionalPosition (c.arclengthCentroid t)
    let T := p.fractionalTangent
    (∫x in (0:ℝ)..1,‖G x+Complex.I*T x‖^2) ≤ (755/1000)^2 *
      (c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2) := by
  let p := c.materialSlice ht
  let T := p.fractionalTangent
  let B := c.arclengthCentroid t
  let G := p.fractionalPosition B
  let D := c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2
  have ct : Continuous T := continuous_iff_continuousAt.mpr
    fun x=>(p.fractionalTangent_hasDerivAt x).continuousAt
  have gz : LowDefect.Tangent.coeff G 0=0 := by
    have m := c.material_fractional_position_mean ht
    change (∫x in (0:ℝ)..1,G x)=0 at m
    simp [LowDefect.Tangent.coeff,fourierCoeffOn_eq_integral,m]
  obtain ⟨h0,hm,h1,h2⟩:=c.material_tangent_fourier_data ht turn
  have bnd := LowDefect.Tangent.normal_correction_moment ct (p.fractionalPosition_der B)
    (p.fractionalPosition_per B) gz h0 hm h1 h2
  have c2 := (c.quarter_second_harmonic_bounds ht turn small).2
  change ‖LowDefect.Tangent.coeff T 2‖ ≤ (28/100)*D at c2
  have c2sq := pow_le_pow_left₀ (norm_nonneg _) c2 2
  have d0 : 0≤D := div_nonneg (c.curvatureOscillation_nonneg ht _) (sq_nonneg _)
  change D≤1/4 at small
  change _≤5/9*D+7/12*‖LowDefect.Tangent.coeff T 2‖^2 at bnd
  change _≤(755/1000)^2*D
  nlinarith only [bnd,c2sq,mul_le_mul_of_nonneg_right small d0,d0]

end MigrationGeometry.Flow.SmoothPeriodicImmersion

namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem quarter_material_normalized_support {t : ℝ} (ht : t∈I)
    (turn : c.signedCurvatureIntegral t=2*Real.pi)
    (small : c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2≤1/4) :
    let p := c.materialSlice ht
    let G := p.fractionalPosition (c.arclengthCentroid t)
    let D := c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2
    let H := 575/1000*Real.sqrt D+140/1000*D
    (∀x∈Icc (0:ℝ) 1, ‖G x‖≤1+H) ∧
    ∀e : ℂ, ‖e‖=1 → ∃x∈Ico (0:ℝ) 1, 1-139/1000*D-H ≤ inner ℝ e (G x) := by
  let p := c.materialSlice ht
  let T := p.fractionalTangent
  let B := c.arclengthCentroid t
  let G := p.fractionalPosition B
  let D := c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2
  let H := 575/1000*Real.sqrt D+140/1000*D
  let A := LowDefect.Tangent.coeff G 1
  have dpos : 0≤D := div_nonneg (c.curvatureOscillation_nonneg ht _) (sq_nonneg _)
  change D≤1/4 at small
  have ct : Continuous T := continuous_iff_continuousAt.mpr fun x=>(p.fractionalTangent_hasDerivAt x).continuousAt
  obtain ⟨t0,mass,m1,m2⟩ := c.material_tangent_fourier_data ht turn
  have gz : LowDefect.Tangent.coeff G 0=0 := by
    have m := c.material_fractional_position_mean ht
    change (∫x in (0:ℝ)..1,G x)=0 at m
    simp [LowDefect.Tangent.coeff,fourierCoeffOn_eq_integral,m]
  have cap := c.quarter_second_harmonic_bounds ht turn small
  have err : ∀x∈Ico (0:ℝ) 1, ‖G x-A*fourier 1 (x:AddCircle (1:ℝ))‖≤H :=
    fun _ hx => LowDefect.Tangent.quarter_position_harmonic_error ct (p.fractionalPosition_der B)
      (p.fractionalPosition_per B) gz m2 cap.2 hx
  have an : ‖A‖=‖LowDefect.Tangent.coeff T 1‖ := by
    dsimp only [A,G]
    rw [LowDefect.Tangent.position_coefficient ct (p.fractionalPosition_der B) (p.fractionalPosition_per B) (by decide : (1:ℤ)≠0)]
    simp
  have mn := mass.summable.sum_le_tsum ({1}:Finset ℤ) (fun n _ => show 0≤LowDefect.Tangent.energy T n from sq_nonneg _)
  rw [mass.tsum_eq] at mn
  simp only [Finset.sum_singleton] at mn
  change ‖LowDefect.Tangent.coeff T 1‖^2≤1 at mn
  have upper : ‖A‖≤1 := by rw [an]; nlinarith
  have low := cap.1
  change 1-‖LowDefect.Tangent.coeff T 1‖^2≤27/100*D at low
  have lower : 1-139/1000*D≤‖A‖ := by
    rw [an]
    apply le_of_sq_le_sq _ (norm_nonneg _)
    nlinarith only [low,mul_le_mul_of_nonneg_right small dpos,dpos]
  change (∀x∈Icc (0:ℝ) 1, ‖G x‖≤1+H) ∧ _
  constructor
  · intro x hx
    have b (s) (hs : s∈Ico (0:ℝ) 1) := (LowDefect.Tangent.harmonic_outer err s hs).trans (add_le_add upper (le_refl H))
    rcases lt_or_eq_of_le hx.2 with l|eq
    · exact b x ⟨hx.1,l⟩
    · subst x
      rw [show G 1=G 0 from p.fractionalPosition_per B]
      exact b 0 ⟨le_rfl,by norm_num⟩
  · intro e unit
    obtain ⟨x,hx,val⟩ := LowDefect.Tangent.harmonic_support err e unit
    exact ⟨x,hx,(sub_le_sub_right lower H).trans val⟩

end MigrationGeometry.Flow.SmoothPeriodicImmersion

namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem quarter_directional_flux_bound {t : ℝ} (ht : t∈I)
    (turn : c.signedCurvatureIntegral t=2*Real.pi)
    (small : c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2≤1/4)
    (e : ℂ) (he : ‖e‖=1) :
    let D := c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2
    let x := Real.sqrt D
    Real.sqrt (c.centroidFluxMoment (innerSL ℝ e) t) ≤
      x*(1755/1000+575/1000*x+140/1000*x^2)*Real.sqrt (c.coreLength t) := by
  let p := c.materialSlice ht
  let a := 2*Real.pi
  let D := c.curvatureOscillation a t/a^2
  let H := 575/1000*Real.sqrt D+140/1000*D
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
  have upper := (c.quarter_material_normalized_support ht turn small).1
  have normFlux := LowDefect.quarter_flux_norm_sq ck cg cz Mp upper moment (c.quarter_material_normal_correction ht turn small)
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
  change p.length*(∫s in (0:ℝ)..1,Q (u s)^2) ≤ p.length*((M+755/1000)^2*D) at scaled
  rw [convertMoment] at scaled
  have L : p.length=c.coreLength t := rfl
  rw [L] at scaled
  change Real.sqrt _≤Real.sqrt D*_*Real.sqrt (c.coreLength t)
  rw [Real.sq_sqrt Dp]
  have mp : 0≤1755/1000+575/1000*Real.sqrt D+140/1000*D := by positivity
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · rw [mul_pow,mul_pow,Real.sq_sqrt Dp,Real.sq_sqrt (c.coreLength_pos ht).le]
    dsimp only [M,H] at scaled
    linarith only [scaled]

end MigrationGeometry.Flow.SmoothPeriodicImmersion

namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem quarter_directional_support {t : ℝ} (ht : t∈I)
    (turn : c.signedCurvatureIntegral t=2*Real.pi)
    (small : c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2≤1/4)
    (e : ℂ) (he : ‖e‖=1) :
    let D := c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2
    ∃u∈Icc 0 c.period, inner ℝ e (c.arclengthCentroid t)+
      c.coreLength t/(2*Real.pi)*(1-575/1000*Real.sqrt D-279/1000*D) ≤ inner ℝ e (c.position t u) := by
  let p := c.materialSlice ht
  let D := c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2
  obtain ⟨x,hx,val⟩ := (c.quarter_material_normalized_support ht turn small).2 e he
  let u := p.arclengthInverse (p.length*x)
  have ord : Monotone p.arclengthInverse := p.arclengthOrderIso.symm.monotone
  have ll : 0≤u := by
    rw [←p.inverse_zero]; exact ord (mul_nonneg p.length_pos.le hx.1)
  have rr : u≤p.period := by
    rw [←p.inverse_length]; exact ord (by simpa using mul_le_mul_of_nonneg_left hx.2.le p.length_pos.le)
  refine ⟨u,⟨ll,rr⟩,?_⟩
  change 1-139/1000*D-(575/1000*Real.sqrt D+140/1000*D) ≤
    inner ℝ e ((2*Real.pi/p.length) • (p.position u-c.arclengthCentroid t)) at val
  rw [real_inner_smul_right,inner_sub_right] at val
  have a : 0<2*Real.pi := by positivity
  have pos : 0≤p.length/(2*Real.pi) := div_nonneg p.length_pos.le a.le
  have h := mul_le_mul_of_nonneg_left val pos
  rw [←mul_assoc,div_mul_div_cancel₀ a.ne',div_self p.length_pos.ne',one_mul] at h
  change inner ℝ e (c.arclengthCentroid t)+p.length/(2*Real.pi)*(1-575/1000*Real.sqrt D-279/1000*D) ≤ inner ℝ e (p.position u)
  linarith only [h]

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.quarter_directional_flux_bound
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.quarter_directional_support
