import Migration.VirialPhysicalModes
import Migration.VirialFourierCorrelation
import Migration.VirialSliceIdentity

noncomputable section
open Set MeasureTheory
open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
open LowDefect LowDefect.Correlation
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem quarter_cubic_material {t : ℝ} (ht : t∈I)
    (turn : c.signedCurvatureIntegral t=2*Real.pi)
    (small : c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2≤1/4) :
    let p:=c.materialSlice ht
    let G:=p.fractionalPosition (c.arclengthCentroid t)
    let T:=p.fractionalTangent
    ‖∫x in (0:ℝ)..1,conj (G x)*T x^2‖≤95/100*(c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2) := by
  let p:=c.materialSlice ht
  let B:=c.arclengthCentroid t
  let T : C(ℝ,ℂ):=⟨p.fractionalTangent,continuous_iff_continuousAt.mpr fun x=>(p.fractionalTangent_hasDerivAt x).continuousAt⟩
  let G : C(ℝ,ℂ):=⟨p.fractionalPosition B,continuous_iff_continuousAt.mpr fun x=>(p.fractionalPosition_der B x).continuousAt⟩
  let e : C(ℝ,ℂ):=⟨fun x : ℝ=>fourier 1 (x : AddCircle ((1:ℝ)-0)),(fourier 1).continuous.comp continuous_quotient_mk'⟩
  have ce : ∀x,‖e x‖=1 := fun _=>Circle.norm_coe _
  have eu : ∀x,‖T x‖=1 := fun _=>tangent_unit p.regular _
  have e0 : mean e=0 := by
    have h:=Tangent.constant_nonzero_coefficient (n:= -1) (by decide)
    change (∫x in (0:ℝ)..1,e x)=0
    simpa only [Tangent.coeff,fourierCoeffOn_eq_integral,neg_neg,sub_zero,div_one,one_smul,
      smul_eq_mul,mul_one,e,ContinuousMap.coe_mk] using h
  have one (f : C(ℝ,ℂ)) : mean (star e*f)=Tangent.coeff f 1 := by
    change (∫x in (0:ℝ)..1,conj (e x)*f x)=_
    simp only [Tangent.coeff,fourierCoeffOn_eq_integral,sub_zero,div_one,one_smul,smul_eq_mul,e,ContinuousMap.coe_mk,←fourier_neg]
  have two (f : C(ℝ,ℂ)) : mean ((star e)^2*f)=Tangent.coeff f 2 := by
    change (∫x in (0:ℝ)..1,(conj (e x))^2*f x)=_
    simp only [Tangent.coeff,fourierCoeffOn_eq_integral,sub_zero,div_one,one_smul,smul_eq_mul,e,ContinuousMap.coe_mk,←fourier_neg,pow_two,←fourier_add]
    rfl
  have massb : mass G≤1 := by
    have W:=periodic_wirtinger (L:=(1:ℝ)) zero_lt_one (fun x=>G x) (fun x=>(2*Real.pi:ℂ)*T x)
      (p.fractionalPosition_per B) (p.fractionalPosition_der B) (continuous_const.mul T.continuous)
      (c.material_fractional_position_mean ht)
    have n (x : ℝ) : ‖(2*Real.pi:ℂ)*T x‖^2=(2*Real.pi)^2 := by
      rw [norm_mul,eu,mul_one,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    simp only [n,intervalIntegral.integral_const,sub_zero,one_smul,one_pow,one_mul] at W
    change (∫x in (0:ℝ)..1,‖G x‖^2)≤1
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos (by positivity : 0<2*Real.pi))).mp
    linarith only [W]
  have coeff (n : ℤ) (hn : n≠0) : Tangent.coeff G n=(-Complex.I/(n:ℂ))*Tangent.coeff T n :=
    Tangent.position_coefficient T.continuous (p.fractionalPosition_der B) (p.fractionalPosition_per B) hn
  have h:=cubic_bound G T e ce eu e0 p.fractionalTangent_mean massb
    (by rw [one,one,coeff 1 (by decide)];simp)
  rw [one,two,coeff 2 (by decide),norm_mul] at h
  norm_num [norm_div] at h
  obtain ⟨W,Z⟩:=c.quarter_second_harmonic_bounds ht turn small
  change 1-‖Tangent.coeff T 1‖^2≤_ at W
  change ‖Tangent.coeff T 2‖≤_ at Z
  change ‖mean (star G*T^2)‖≤_
  linarith only [h,W,Z]

theorem quarter_support_flux_mean {t : ℝ} (ht : t∈I)
    (turn : c.signedCurvatureIntegral t=2*Real.pi)
    (small : c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2≤1/4) :
    let p:=c.materialSlice ht
    let G:=p.fractionalPosition (c.arclengthCentroid t)
    let T:=p.fractionalTangent
    let K:=fun x=>p.fractionalCurvature x/(2*Real.pi)
    ‖∫x in (0:ℝ)..1,(inner ℝ (Complex.I*T x) (G x)) • ((K x:ℂ)*G x+Complex.I*T x)‖≤
      95/100*(c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2) := by
  let p:=c.materialSlice ht
  let G:=p.fractionalPosition (c.arclengthCentroid t)
  let T:=p.fractionalTangent
  let K:=fun x=>p.fractionalCurvature x/(2*Real.pi)
  have ca : Continuous p.fractionalCurvature := continuous_const.mul
    ((curvature_smooth p.smooth p.regular).continuous.comp (p.inverse_continuous.comp (continuous_const.mul continuous_id)))
  have kt (x : ℝ) : HasDerivAt T (((2*Real.pi:ℝ):ℂ)*(K x:ℂ)*Complex.I*T x) x := by
    apply (p.fractionalTangent_hasDerivAt x).congr_deriv
    dsimp only [K];push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero];rfl
  have per : T 1=T 0 := by
    dsimp only [T,PeriodicRegularPosition.fractionalTangent];rw [mul_one,mul_zero,p.inverse_length,p.inverse_zero]
    simpa using tangent_periodic p.smooth p.periodic 0
  have identity:=slice_identity (a:=2*Real.pi) (by positivity)
    (fun x=>by simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using p.fractionalPosition_der (c.arclengthCentroid t) x)
    kt (ca.div_const _) (fun x=>tangent_unit p.regular _) (p.fractionalPosition_per _) per (c.material_fractional_position_mean ht)
  change ‖∫x in (0:ℝ)..1,(inner ℝ (Complex.I*T x) (G x)) • ((K x:ℂ)*G x+Complex.I*T x)‖≤_
  rw [identity,norm_neg]
  exact c.quarter_cubic_material ht turn small

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.quarter_support_flux_mean

