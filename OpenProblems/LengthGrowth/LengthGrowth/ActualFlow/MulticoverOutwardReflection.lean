import LengthGrowth.ActualFlow.MulticoverAngleRealization

noncomputable section
open MeasureTheory Function
open scoped ComplexConjugate ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.Multicover.Outward
open LengthGrowth.ActualFlow

private theorem conj_deriv {f:ℝ→ℂ} (df:Differentiable ℝ f) (s:ℝ):
    deriv (fun x=>conj (f x)) s=conj (deriv f s):=
  (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s (df s).hasDerivAt).deriv

theorem reflect_material (g:PeriodicRegularPosition) :
    ∃q:PeriodicRegularPosition,q.period=g.period ∧ q.length=g.length ∧
      materialSignedCurvature q.position q.period= -materialSignedCurvature g.position g.period ∧
      materialEnergy q.position q.period=materialEnergy g.position g.period ∧
      materialLengthRate q.position q.period=materialLengthRate g.position g.period ∧
      materialDissipation q.position q.period=materialDissipation g.position g.period:=by
  let γ:=g.position
  let β:=fun x=>conj (γ x)
  have dγ : Differentiable ℝ γ:=g.smooth.differentiable (by simp)
  have derivβ (x:ℝ):deriv β x=conj (deriv γ x):=conj_deriv dγ x
  have sc (x:ℝ) : speed β x=speed γ x:=by simp [speed,derivβ]
  let q:PeriodicRegularPosition:=
    { period:=g.period
      period_pos:=g.period_pos
      position:=β
      smooth:=Complex.conjCLE.contDiff.comp g.smooth
      periodic:=fun x=>congrArg conj (g.periodic x)
      regular:=fun x h=>by rw [derivβ] at h;exact g.regular x (by simpa using congrArg conj h) }
  have tan : tangent β=(fun x=>conj (tangent γ x)):=by
    funext x
    simp [tangent,arcDerivative,derivβ,sc,Complex.real_smul]
  have cur : curvature β=(fun x=> -(curvature γ x)):=by
    funext x
    have td:=(tangent_smooth g.smooth g.regular).differentiable (by simp)
    rw [curvature,curvature,tan,conj_deriv td,sc]
    have eq : conj (conj (tangent γ x))*conj (deriv (tangent γ) x)=conj (conj (tangent γ x)*deriv (tangent γ) x):=by simp
    rw [eq,Complex.conj_im,neg_div]
  have grad : curvatureGradient β=(fun x=> -(curvatureGradient γ x)):=by
    funext x
    simp [curvatureGradient,arcDerivative,cur,sc]
  have forceβ (x:ℝ):force β x= -force γ x:=by
    simp [force,curvatureSecond,arcDerivative,grad,cur,sc]
    ring
  refine ⟨q,rfl,?_,?_,?_,?_,?_⟩
  · change (∫x in 0..g.period,speed β x)=∫x in 0..g.period,speed γ x
    simp only [sc]
  · change (∫x in 0..g.period,curvature β x*speed β x)= -(∫x in 0..g.period,curvature γ x*speed γ x)
    simp only [cur,sc,neg_mul,intervalIntegral.integral_neg]
  · change 1/2*(∫x in 0..g.period,curvature β x^2*speed β x)=1/2*(∫x in 0..g.period,curvature γ x^2*speed γ x)
    simp only [cur,sc,neg_sq]
  · change (∫x in 0..g.period,curvature β x*force β x*speed β x)=∫x in 0..g.period,curvature γ x*force γ x*speed γ x
    simp only [cur,sc,forceβ,neg_mul_neg]
  · change (∫x in 0..g.period,force β x^2*speed β x)=∫x in 0..g.period,force γ x^2*speed γ x
    simp only [forceβ,sc,neg_sq]
end LengthGrowth.Multicover.Outward
#print axioms LengthGrowth.Multicover.Outward.reflect_material
