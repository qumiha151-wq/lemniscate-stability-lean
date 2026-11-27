import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination

noncomputable section
open Complex Set Filter Metric
open scoped Topology
namespace ClosedSimilarity.LemniscaticExtension
set_option backward.isDefEq.respectTransparency false

structure OscillatorGerm where
  u : ℂ→ℂ
  v : ℂ→ℂ
  hu : AnalyticAt ℂ u 0
  hv : AnalyticAt ℂ v 0
  zero : u 0=0
  one : v 0=1
  energy : ∀ᶠ z in 𝓝 0,v z^2+u z^4=1
  laws : ∀ᶠ z in 𝓝 0,HasDerivAt u (v z) z ∧ HasDerivAt v (-2*u z^3) z

private def radical (z : ℂ) : ℂ := (1-z^4)^((2:ℂ)⁻¹)
private theorem rad_zero : radical 0=1 := by simp [radical]
private theorem rad_sq (z : ℂ) : radical z^2=1-z^4 := by simp [radical]
private theorem rad_analytic : AnalyticAt ℂ radical 0 := by
  unfold radical
  apply AnalyticAt.cpow (analyticAt_const.sub (analyticAt_id.pow 4)) analyticAt_const
  simp

/-- Local complex inversion of the normalized quartic elliptic integral. -/
theorem local_oscillator_exists : Nonempty OscillatorGerm := by
  let h := fun z=>(radical z)⁻¹
  have ha : AnalyticAt ℂ h 0 := rad_analytic.inv (by simp [rad_zero])
  obtain ⟨r,rp,rball⟩ := Metric.mem_nhds_iff.mp ha.eventually_analyticAt
  have hd : DifferentiableOn ℂ h (ball 0 r) := fun z hz=>(rball hz).differentiableAt.differentiableWithinAt
  obtain ⟨p,p0,pd⟩ := hd.isExactOn_ball.with_val_at 0 0
  have center : (0:ℂ)∈ball 0 r := mem_ball_self rp
  have pa : AnalyticAt ℂ p 0 := (show DifferentiableOn ℂ p (ball 0 r) from
    fun z hz=>(pd z hz).differentiableAt.differentiableWithinAt).analyticAt (ball_mem_nhds _ rp)
  have dp : deriv p 0=1 := by rw [(pd 0 center).deriv]; simp [h,rad_zero]
  have dn : deriv p 0≠0 := by rw [dp]; exact one_ne_zero
  let u := pa.hasStrictDerivAt.localInverse p (deriv p 0) 0 dn
  have ua : AnalyticAt ℂ u 0 := p0 ▸ pa.analyticAt_localInverse dn
  have inv : ∀ᶠ z in 𝓝 (0:ℂ),p (u z)=z := p0 ▸ pa.hasStrictDerivAt.eventually_right_inverse dn
  have init : u 0=0 := by
    have le := (pa.hasStrictDerivAt.eventually_left_inverse dn).self_of_nhds
    simpa only [p0] using le
  have to0 : Tendsto u (𝓝 0) (𝓝 0) := by simpa only [init] using ua.continuousAt.tendsto
  let v := fun z=>radical (u z)
  have va : AnalyticAt ℂ v 0 := (show AnalyticAt ℂ radical (u 0) by rw [init];exact rad_analytic).comp ua
  have v0 : v 0=1 := by simp [v,init,rad_zero]
  have nview : ∀ᶠ z in 𝓝 0,v z≠0 := va.continuousAt.eventually_ne (by rw [v0];exact one_ne_zero)
  have eql : (fun z=>p (u z))=ᶠ[𝓝 0] id := inv
  have uder : ∀ᶠ z in 𝓝 0,HasDerivAt u (v z) z := by
    filter_upwards [ua.eventually_analyticAt,eql.deriv,to0.eventually (ball_mem_nhds _ rp),nview]
      with z uz dz uzr nv
    have chain := (pd _ uzr).comp z uz.differentiableAt.hasDerivAt
    have eq : (v z)⁻¹*deriv u z=1 := chain.deriv.symm.trans (dz.trans (by simp))
    field_simp [nv] at eq
    exact eq ▸ uz.differentiableAt.hasDerivAt
  refine ⟨u,v,ua,va,init,v0,Eventually.of_forall (fun z=>by change radical (u z)^2+_=1;rw [rad_sq];ring),?_⟩
  filter_upwards [uder,va.eventually_analyticAt,nview] with z du av nz
  have dv := av.differentiableAt.hasDerivAt
  have eq : (fun t=>v t^2)=(fun t=>1-u t^4) := funext fun t=>rad_sq _
  have j := dv.pow 2
  change HasDerivAt (fun t=>v t^2) _ z at j
  rw [eq] at j
  have recurrence := j.unique ((hasDerivAt_const z (1:ℂ)).sub (du.pow 4))
  refine ⟨du,?_⟩
  have e : deriv v z= -2*u z^3 := by
    apply mul_left_cancel₀ nz
    linear_combination recurrence/2
  exact e ▸ dv

end ClosedSimilarity.LemniscaticExtension
