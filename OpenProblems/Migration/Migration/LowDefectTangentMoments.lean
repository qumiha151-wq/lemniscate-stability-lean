import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
namespace MigrationGeometry.Flow.LowDefect.Tangent
noncomputable section
open Set MeasureTheory Real
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
def coeff (f : ℝ→ℂ) (n : ℤ) := fourierCoeffOn (by norm_num : (0:ℝ)<1) f n
def omega (n : ℤ)  := 2*Real.pi*(n:ℝ)
def energy (f : ℝ→ℂ) (n : ℤ) := ‖coeff f n‖^2
theorem parseval (f : ℝ→ℂ) (cf : Continuous f) : HasSum (energy f) (∫x in 0..1,‖f x‖^2) := by
  have lp : MemLp f 2 (volume.restrict (Ioc 0 1)) := by
    exact (memLp_two_iff_integrable_sq_norm cf.aestronglyMeasurable).mpr ((cf.norm.pow 2).intervalIntegrable 0 1).1
  change HasSum (fun n=>‖fourierCoeffOn (by norm_num : (0:ℝ)<1) f n‖^2) _
  simpa only [sub_zero,inv_one,one_smul] using hasSum_sq_fourierCoeffOn (by norm_num : (0:ℝ)<1) lp

theorem coeff_der {f g : ℝ→ℂ} (df : ∀x,HasDerivAt f (g x) x) (cg : Continuous g)
    (p : f 1=f 0) (n : ℤ) : coeff g n=(omega n:ℂ)*Complex.I*coeff f n := by
  by_cases hz : n=0
  · subst n
    have eq := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=1)
      (fun x _=>df x) (cg.intervalIntegrable 0 1)
    rw [p,sub_self] at eq
    simp [coeff,omega,fourierCoeffOn_eq_integral,eq]
  · have eq := fourierCoeffOn_of_hasDerivAt (by norm_num : (0:ℝ)<1) hz (fun x _=>df x) (cg.intervalIntegrable 0 1)
    rw [p,sub_self,mul_zero,zero_sub] at eq
    norm_num only [Complex.ofReal_one,Complex.ofReal_zero,sub_zero,one_mul] at eq
    change fourierCoeffOn _ g n=_
    dsimp only [coeff]
    rw [eq]
    have hn : (n:ℂ)≠0 := by exact_mod_cast hz
    have hpi : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
    unfold omega;push_cast
    field_simp [hn,hpi,Complex.I_ne_zero]


theorem coeff_sub {f g : ℝ → ℂ} (cf : Continuous f) (cg : Continuous g) (n : ℤ) :
    coeff (fun x=>f x-g x) n=coeff f n-coeff g n := by
  simp only [coeff,fourierCoeffOn_eq_integral,sub_zero,div_one,one_smul,smul_eq_mul,mul_sub]
  have ct : Continuous (fun x : ℝ=>fourier (-n) (x : AddCircle ((1:ℝ)-0))) :=
    (fourier (-n)).continuous.comp continuous_quotient_mk'
  exact intervalIntegral.integral_sub (μ:=volume) (a:=(0:ℝ)) (b:=1)
    (f:=fun x=>fourier (-n) (x : AddCircle ((1:ℝ)-0))*f x)
    (g:=fun x=>fourier (-n) (x : AddCircle ((1:ℝ)-0))*g x)
    ((ct.mul cf).intervalIntegrable ..) ((ct.mul cg).intervalIntegrable ..)

theorem tangent_data {T : ℝ → ℂ} {k : ℝ → ℝ} (ck : Continuous k)
    (fr : ∀x,HasDerivAt T ((k x : ℂ)*Complex.I*T x) x)
    (unit : ∀x,‖T x‖=1) (per : T 1=T 0) (mean : (∫x in 0..1,k x)=2*Real.pi)
    (closed : (∫x in 0..1,T x)=0) :
    coeff T 0=0 ∧ HasSum (energy T) 1 ∧
    HasSum (fun n : ℤ=>(n:ℝ)*energy T n) 1 ∧
    HasSum (fun n : ℤ=>((n:ℝ)-1)^2*energy T n)
      ((∫x in 0..1,(k x-2*Real.pi)^2)/(2*Real.pi)^2) := by
  let a : ℝ := 2*Real.pi
  have ap : 0<a := by dsimp [a]; positivity
  have ct : Continuous T := continuous_iff_continuousAt.mpr fun x=>(fr x).continuousAt
  let v := fun x=>(k x : ℂ)*Complex.I*T x
  have cv : Continuous v := ((Complex.continuous_ofReal.comp ck).mul continuous_const).mul ct
  let v0 := fun x=>((a:ℂ)*Complex.I)*T x
  have cv0 : Continuous v0 := continuous_const.mul ct
  let z := fun x=>v x-v0 x
  have cz := cv.sub cv0
  have vc (n : ℤ) : coeff v n=(a:ℂ)*(n:ℂ)*Complex.I*coeff T n := by
    simpa only [a,v,omega,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_intCast,mul_assoc]
      using coeff_der fr cv per n
  have zc (n : ℤ) : coeff z n=(a:ℂ)*((n:ℂ)-1)*Complex.I*coeff T n := by
    rw [show coeff z n=coeff v n-coeff v0 n from coeff_sub cv cv0 n,vc]
    have h : coeff v0 n=((a:ℂ)*Complex.I)*coeff T n :=
      fourierCoeffOn.const_mul _ _ _ (by norm_num : (0:ℝ)<1)
    rw [h];ring
  have vv (s : ℝ) : ‖v s‖^2 = (k s)^2 := by simp [v,unit]
  have zz (s : ℝ) : ‖z s‖^2 = (k s-a)^2 := by
    have eqn : z s=(((k s-a:ℝ):ℂ))*Complex.I*T s := by dsimp [z,v,v0];push_cast;ring
    rw [eqn,norm_mul,norm_mul,unit,Complex.norm_I,Complex.norm_real,
      Real.norm_eq_abs,mul_one,mul_one,sq_abs]
  have vmode (n : ℤ) : energy v n=a^2*(n:ℝ)^2*energy T n := by
    simp [energy,vc,mul_pow,Complex.norm_intCast]
  have zmode (n : ℤ) : energy z n=a^2*((n:ℝ)-1)^2*energy T n := by
    have nreal : (n:ℂ)-1=(((n:ℝ)-1:ℝ):ℂ) := by push_cast; rfl
    unfold energy
    rw [zc,nreal,norm_mul,norm_mul,norm_mul,Complex.norm_I,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,mul_one,mul_pow,mul_pow,sq_abs,sq_abs]
  have hu := parseval T ct
  simp only [unit,one_pow,intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one] at hu
  have hv := parseval v cv
  change HasSum (fun n=>energy v n) _ at hv
  simp only [vmode,vv] at hv
  have hz := parseval z cz
  change HasSum (fun n=>energy z n) _ at hz
  simp only [zmode,zz] at hz
  have scale (q : ℤ → ℝ) (P : ℝ)
      (h : HasSum (fun n=>a^2*q n*energy T n) P) :
      HasSum (fun n=>q n*energy T n) (P/a^2) := by
    have hh := h.mul_left (a^2)⁻¹
    simpa only [←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ ap.ne'),one_mul,div_eq_inv_mul] using hh
  have h1 := scale _ _ hv
  have h2 := scale _ _ hz
  have delta : (∫x in 0..1,k x^2)-(∫x in 0..1,(k x-a)^2)=a^2 := by
    rw [←intervalIntegral.integral_sub (f:=fun x=>k x^2) (g:=fun x=>(k x-a)^2)
      ((ck.pow 2).intervalIntegrable ..) (((ck.sub continuous_const).pow 2).intervalIntegrable ..)]
    rw [show (fun x=>k x^2-(k x-a)^2)=fun x=>(2*a)*k x-a^2 by funext;ring,
      intervalIntegral.integral_sub (f:=fun x=>(2*a)*k x) (g:=fun _=>a^2)
        ((ck.const_mul _).intervalIntegrable ..) (continuous_const.intervalIntegrable ..),
      intervalIntegral.integral_const_mul,mean]
    simp [a]; ring
  have mom := (((h1.sub h2).add hu).mul_left (1/2:ℝ))
  have pn (n : ℤ) : (1/2:ℝ)*(((n:ℝ)^2*energy T n-((n:ℝ)-1)^2*energy T n)+energy T n)=
      (n:ℝ)*energy T n := by ring
  simp only [pn] at mom
  have rhs : (1/2:ℝ)*(((∫ x in 0..1,k x^2)/a^2-(∫ x in 0..1,(k x-a)^2)/a^2)+1)=1 := by
    rw [← sub_div,delta,div_self (pow_ne_zero _ ap.ne')];norm_num
  rw [rhs] at mom
  exact ⟨by simp [coeff,fourierCoeffOn_eq_integral,closed],hu,mom,h2⟩

end
end MigrationGeometry.Flow.LowDefect.Tangent
#print axioms MigrationGeometry.Flow.LowDefect.Tangent.tangent_data
