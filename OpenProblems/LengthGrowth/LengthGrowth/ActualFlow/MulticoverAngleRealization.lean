import LengthGrowth.ActualFlow.MulticoverSharpLength
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

noncomputable section
open Set Filter Function MeasureTheory Topology
open scoped ContDiff ComplexConjugate
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.Multicover.Outward
open LengthGrowth.ActualFlow

def primitive {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (v:ℝ→E) (s:ℝ):=∫x in 0..s,v x

theorem primitive_derivative {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {v:ℝ→E} (cv:Continuous v) (s:ℝ):HasDerivAt (primitive v) (v s) s:=
  intervalIntegral.integral_hasDerivAt_right (cv.intervalIntegrable _ _) cv.stronglyMeasurable.stronglyMeasurableAtFilter cv.continuousAt

theorem primitive_smooth {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {v:ℝ→E} (sm:ContDiff ℝ ∞ v):ContDiff ℝ ∞ (primitive v):=by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x=>(primitive_derivative sm.continuous x).differentiableAt,?_⟩
  rwa [show deriv (primitive v)=v by funext x;exact (primitive_derivative sm.continuous x).deriv]

def angleTangent (θ:ℝ→ℝ) (s:ℝ):=Complex.exp (Complex.I*(θ s:ℂ))

theorem angleTangent_unit (θ:ℝ→ℝ) (s:ℝ):‖angleTangent θ s‖=1:=by simp [angleTangent,Complex.norm_exp]

theorem angleTangent_smooth {θ:ℝ→ℝ} (sm:ContDiff ℝ ∞ θ):ContDiff ℝ ∞ (angleTangent θ):=by
  unfold angleTangent
  have rc : ContDiff ℝ ∞ (fun x=>(θ x:ℂ)):=Complex.ofRealCLM.contDiff.comp sm
  fun_prop

theorem primitive_periodic {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P:ℝ} {v:ℝ→E} (cv:Continuous v) (pv:Periodic v P) (zero:(∫s in 0..P,v s)=0) : Periodic (primitive v) P:=by
  intro s
  simpa only [primitive,zero_add,zero,add_zero] using pv.intervalIntegral_add_eq_add 0 s cv.intervalIntegrable

theorem realize_angle (P:ℝ) (hp:0<P) (θ k:ℝ→ℝ) (sm:ContDiff ℝ ∞ θ) (dk:deriv θ=k)
    (per:Periodic (angleTangent θ) P) (close:(∫s in 0..P,angleTangent θ s)=0) :
    let F:=fun s=>deriv (deriv k) s+k s^3/2
    ∃g:PeriodicRegularPosition,g.period=P ∧ g.length=P ∧
      materialSignedCurvature g.position g.period=(∫s in 0..P,k s) ∧
      materialEnergy g.position g.period=(1/2:ℝ)*(∫s in 0..P,k s^2) ∧
      materialLengthRate g.position g.period=(∫s in 0..P,k s*F s) ∧
      materialDissipation g.position g.period=(∫s in 0..P,F s^2) :=by
  let v:=angleTangent θ
  let γ:=primitive v
  have vs : ContDiff ℝ ∞ v:=angleTangent_smooth sm
  have dg : deriv γ=v:=funext fun s=>(primitive_derivative vs.continuous s).deriv
  have unit (s:ℝ):‖deriv γ s‖=1:=by rw [dg];exact angleTangent_unit θ s
  let g : PeriodicRegularPosition:=
    {period:=P,period_pos:=hp,position:=γ,smooth:=primitive_smooth vs,
     periodic:=primitive_periodic vs.continuous per close,regular:=fun s h=>by simpa [h] using unit s}
  have dv (s:ℝ): HasDerivAt v (v s*(Complex.I*(k s:ℂ))) s:=by
    have h:=(sm.differentiable (by simp) s).hasDerivAt
    rw [dk] at h
    exact ((h.ofReal_comp.const_mul Complex.I).cexp)
  have kj : curvature γ=k:=by
    funext s
    rw [←legacy_curvature_eq_actual unit s]
    unfold LengthGrowth.positionCurvature
    rw [dg,(dv s).deriv,←mul_assoc,mul_comm (conj (v s)),Complex.mul_conj,←Complex.sq_norm,angleTangent_unit]
    simp
  have speed1 (s:ℝ):speed γ s=1:=unit s
  have ff (s:ℝ):force γ s=deriv (deriv k) s+k s^3/2:=by rw [force,unit_speed_curvatureSecond unit,kj]
  refine ⟨g,rfl,?_,?_,?_,?_,?_⟩
  · change (∫s in 0..P,speed γ s)=P
    simp [speed1]
  · change (∫s in 0..P,curvature γ s*speed γ s)=_
    simp only [kj,speed1,mul_one]
  · change 1/2*(∫s in 0..P,curvature γ s^2*speed γ s)=_
    simp only [kj,speed1,mul_one]
  · change (∫s in 0..P,curvature γ s*force γ s*speed γ s)=_
    simp only [kj,ff,speed1,mul_one]
  · change (∫s in 0..P,force γ s^2*speed γ s)=_
    simp only [ff,speed1,mul_one]
end LengthGrowth.Multicover.Outward
#print axioms LengthGrowth.Multicover.Outward.realize_angle
