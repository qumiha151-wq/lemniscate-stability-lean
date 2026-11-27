import Migration.LowDefectMaterialFlux
import Mathlib.Analysis.Calculus.Deriv.Star

noncomputable section
open Set MeasureTheory
open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.LowDefect.Correlation

/-- Integration by parts converts the projected normal virial correlation into a cubic
moment of position and tangent. The parameter is fractional arclength. -/
theorem slice_identity {G T : ℝ→ℂ} {K : ℝ→ℝ} {a : ℝ} (ap : 0<a)
    (dG : ∀x,HasDerivAt G ((a:ℂ)*T x) x)
    (dT : ∀x,HasDerivAt T ((a:ℂ)*(K x:ℂ)*Complex.I*T x) x)
    (ck : Continuous K) (unit : ∀x,‖T x‖=1)
    (gper : G 1=G 0) (tper : T 1=T 0) (g0 : (∫x in (0:ℝ)..1,G x)=0) :
    (∫x in (0:ℝ)..1,(inner ℝ (Complex.I*T x) (G x)) • ((K x:ℂ)*G x+Complex.I*T x)) =
       -(∫x in (0:ℝ)..1,conj (G x)*T x^2) := by
  let P:=fun x=>inner ℝ (Complex.I*T x) (G x)
  let H:=fun x=>(K x:ℂ)*G x+Complex.I*T x
  let V:=fun x=>(conj (G x)*T x+conj (T x)*G x)*G x
  let C:=fun x=>conj (G x)*T x^2
  have cg := continuous_iff_continuousAt.mpr (fun x=>(dG x).continuousAt)
  have ct := continuous_iff_continuousAt.mpr (fun x=>(dT x).continuousAt)
  have cp : Continuous P := (continuous_const.mul ct).inner cg
  have ch : Continuous H := ((Complex.continuous_ofReal.comp ck).mul cg).add (continuous_const.mul ct)
  have cc : Continuous C := (Complex.continuous_conj.comp cg).mul (ct.pow 2)
  have d (x : ℝ) : HasDerivAt V ((2*(a:ℂ))*(P x • H x+G x+C x)) x := by
    have der:=((((dG x).star.mul (dT x)).add ((dT x).star.mul (dG x))).mul (dG x))
    apply der.congr_deriv
    have normal : (P x:ℂ)=(G x*conj (Complex.I*T x)+conj (G x)*Complex.I*T x)/2 := by
      change (((G x*conj (Complex.I*T x)).re:ℝ):ℂ)=_
      rw [Complex.re_eq_add_conj];simp only [map_mul,Complex.conj_conj];ring
    have tu : T x*conj (T x)=1 := by rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,unit];norm_num
    change ((conj ((a:ℂ)*T x)*T x+conj (G x)*((a:ℂ)*(K x:ℂ)*Complex.I*T x))+
      (conj ((a:ℂ)*(K x:ℂ)*Complex.I*T x)*G x+conj (T x)*((a:ℂ)*T x)))*G x+
      (conj (G x)*T x+conj (T x)*G x)*((a:ℂ)*T x)=_
    rw [Complex.real_smul,normal]
    dsimp only [H,C]
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
    linear_combination (2*(a:ℂ)*G x)*tu + (a:ℂ)*(G x*conj (T x)*T x-conj (G x)*T x^2)*(Complex.I_sq)
  have diff := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=(0:ℝ)) (b:=1)
    (fun x _=>d x) ((continuous_const.mul (((cp.smul ch).add cg).add cc)).intervalIntegrable ..)
  have per : V 1=V 0 := by dsimp only [V];rw [gper,tper]
  rw [per,sub_self] at diff
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add (f:=fun x=>P x • H x+G x)
      (g:=C) (((cp.smul ch).add cg).intervalIntegrable ..) (cc.intervalIntegrable ..),
    intervalIntegral.integral_add (f:=fun x=>P x • H x) (g:=G) ((cp.smul ch).intervalIntegrable ..) (cg.intervalIntegrable ..),g0,add_zero] at diff
  have nz : 2*(a:ℂ)≠0 := mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr ap.ne')
  exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp diff).resolve_left nz)

end MigrationGeometry.Flow.LowDefect.Correlation
#print axioms MigrationGeometry.Flow.LowDefect.Correlation.slice_identity

