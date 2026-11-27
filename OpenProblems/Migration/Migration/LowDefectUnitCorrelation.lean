import Migration.LowDefectTangentMoments
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
open Set MeasureTheory
open scoped ComplexConjugate
namespace MigrationGeometry.Flow.LowDefect.Tangent

private def ave : C(ℝ,ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫x in (0:ℝ)..1,f x
  map_add' f g := intervalIntegral.integral_add (f.continuous.intervalIntegrable ..)
    (g.continuous.intervalIntegrable ..)
  map_smul' a f := by
    change (∫x in (0:ℝ)..1,a • f x)=_
    rw [intervalIntegral.integral_smul]; rfl

private def cn (a : ℂ) : C(ℝ,ℂ) := ContinuousMap.const ℝ a
private theorem ave_const (a : ℂ) : ave (cn a)=a := by simp [ave,cn]
private theorem ave_cn_mul (a : ℂ) (f : C(ℝ,ℂ)) : ave (cn a*f)=a*ave f := by
  change ave (a • f)=a*ave f
  rw [map_smul,smul_eq_mul]
private theorem ave_star (f : C(ℝ,ℂ)) : ave (star f)=conj (ave f) := by
  exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).intervalIntegral_comp_comm (μ:=volume)
    (a:=0) (b:=1) (f.continuous.intervalIntegrable ..)
private theorem ave_one : ave 1=1 := ave_const 1

/-- For unit-valued T,E of zero mean, set A=mean(conj(E)T),
B=mean(conj(E)^2 T). The middle coefficient is quadratically suppressed
by leaked Fourier mass. No product Fourier inversion is required. -/
theorem unit_correlation (T e : C(ℝ,ℂ)) (t0 : (∫x in (0:ℝ)..1,T x)=0)
    (e0 : (∫x in (0:ℝ)..1,e x)=0) (tu : ∀x,‖T x‖=1) (eu : ∀x,‖e x‖=1) :
    let A := ∫x in (0:ℝ)..1,conj (e x)*T x
    let B := ∫x in (0:ℝ)..1,(conj (e x))^2*T x
    ‖B‖*‖A‖ ≤ 1-‖A‖^2 := by
  let A := ave (star e*T)
  let B := ave ((star e)^2*T)
  let R := T-cn A*e
  have units (f : C(ℝ,ℂ)) (hf : ∀x,‖f x‖=1) : f*star f=1 := by
    ext x
    change f x * conj (f x)=1
    rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,hf]; norm_num
  have tt := units T tu
  have ee := units e eu
  have ss : star (cn A)=cn (conj A) := rfl
  have rev : ave (e*star T)=conj A := by
    have h:=ave_star (star e*T)
    simpa [A,mul_comm] using h
  have meanOne : ave T=0 := t0
  have meanE : ave e=0 := e0
  have conjE : ave (star e)=0 := by rw [ave_star,meanE]; simp
  have conjT : ave (star T)=0 := by rw [ave_star,meanOne]; simp
  have de : R*star R =
      1-cn (conj A)*(star e*T)-cn A*(e*star T)+cn (A*conj A) := by
    dsimp only [R]; rw [star_sub,star_mul',ss]
    have cm : cn (A*conj A)=cn A*cn (conj A) := rfl
    rw [cm]
    linear_combination tt + (cn A*cn (conj A))*ee
  have dw : star e*(R*star R) =
      star e-cn (conj A)*((star e)^2*T)-cn A*star T+cn (A*conj A)*star e := by
    rw [de]
    linear_combination -(cn A*star T)*ee
  have mass : ave (R*star R)=1-A*conj A := by
    rw [de,map_add,map_sub,map_sub,ave_one,ave_cn_mul,ave_cn_mul,ave_const,rev]
    change 1-conj A*A-A*conj A+A*conj A=1-A*conj A
    ring
  have weighted : ave (star e*(R*star R)) = -conj A*B := by
    rw [dw,map_add,map_sub,map_sub,ave_cn_mul,ave_cn_mul,ave_cn_mul,conjE,conjT]
    change 0-conj A*B-A*0+(A*conj A)*0= -conj A*B
    ring
  have hs : (∫x in (0:ℝ)..1,‖R x‖^2)=1-‖A‖^2 := by
    have cr : Continuous (fun x=>R x * conj (R x)) := R.continuous.mul (Complex.continuous_conj.comp R.continuous)
    have re := Complex.reCLM.intervalIntegral_comp_comm (a:=0) (b:=1) (μ:=volume) (cr.intervalIntegrable ..)
    change _ = (ave (R*star R)).re at re
    rw [mass,Complex.mul_conj,Complex.normSq_eq_norm_sq] at re
    simpa only [Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.reCLM_apply,
      Complex.sub_re,Complex.one_re,Complex.ofReal_re,←Complex.ofReal_pow] using re
  have bound := intervalIntegral.norm_integral_le_integral_norm (μ:=volume)
    (f:=fun x : ℝ=>conj (e x)*(R x*conj (R x))) (by norm_num : (0:ℝ)≤1)
  change ‖ave (star e*(R*star R))‖≤_ at bound
  rw [weighted] at bound
  have rn (x : ℝ) : ‖conj (e x)*(R x*conj (R x))‖=‖R x‖^2 := by
    rw [norm_mul,norm_mul,Complex.norm_conj,Complex.norm_conj,eu,one_mul,sq]
  simp only [rn,hs,norm_mul,norm_neg,Complex.norm_conj] at bound
  change ‖B‖*‖A‖≤1-‖A‖^2
  simpa only [mul_comm] using bound

end MigrationGeometry.Flow.LowDefect.Tangent
#print axioms MigrationGeometry.Flow.LowDefect.Tangent.unit_correlation
