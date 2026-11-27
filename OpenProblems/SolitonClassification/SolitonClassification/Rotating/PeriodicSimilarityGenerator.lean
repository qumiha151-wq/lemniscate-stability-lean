import SolitonClassification.Rotating.RotatingNormalEvolutionScalar

namespace ClosedSimilarity
noncomputable section
open Real
open scoped ContDiff
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- On every smooth periodic unit-speed plane curve with nonconstant signed
curvature, the normal component of a similarity generator determines its
two translation coefficients, dilation and rotation. -/
theorem tangent_similarity_zero {x y : ℝ→ℝ} {L a b u v : ℝ} (hL : 0<L)
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y) (px' : Function.Periodic x L)
    (py' : Function.Periodic y L) (speed : ∀s, deriv x s^2+deriv y s^2=1)
    (different : ∃s t, deriv x s*deriv (deriv y) s-deriv y s*deriv (deriv x) s ≠
      deriv x t*deriv (deriv y) t-deriv y t*deriv (deriv x) t)
    (tangent : ∀s, -(a*x s-b*y s+u)*deriv y s+(b*x s+a*y s+v)*deriv x s=0) :
    a=0 ∧ b=0 ∧ u=0 ∧ v=0 := by
  let C := deriv x
  let S := deriv y
  let k := fun s => C s*deriv S s-S s*deriv C s
  change ∃s t,k s≠k t at different
  let X := fun s => a*x s-b*y s+u
  let Y := fun s => b*x s+a*y s+v
  let w := fun s => X s*C s+Y s*S s
  let n := fun s => -(X s)*S s+Y s*C s
  have normal (s : ℝ) : n s=0 := tangent s
  have unit (s : ℝ) : (S s)^2+(C s)^2=1 := by linarith only [speed s]
  have smoothC : ContDiff ℝ ∞ C := hx.deriv'
  have smoothS : ContDiff ℝ ∞ S := hy.deriv'
  have dc (s : ℝ) : HasDerivAt C (deriv C s) s := (smoothC.differentiable (by simp) s).hasDerivAt
  have ds (s : ℝ) : HasDerivAt S (deriv S s) s := (smoothS.differentiable (by simp) s).hasDerivAt
  have orth (s : ℝ) : C s*deriv C s+S s*deriv S s=0 := by
    have h := (((dc s).pow 2).add ((ds s).pow 2)).deriv
    have e : (fun u => C u^2+S u^2)=fun _ => (1:ℝ) := funext speed
    change deriv (fun u => C u^2+S u^2) s=_ at h
    rw [e,deriv_const'] at h
    norm_num at h
    nlinarith only [h]
  have dC (s : ℝ) : HasDerivAt C (-(S s)*k s) s := by
    convert! dc s using 1
    change -S s*(C s*deriv S s-S s*deriv C s)=deriv C s
    linear_combination deriv C s*unit s-C s*orth s
  have dS (s : ℝ) : HasDerivAt S (C s*k s) s := by
    convert! ds s using 1
    change C s*(C s*deriv S s-S s*deriv C s)=deriv S s
    linear_combination deriv S s*unit s-S s*orth s
  have dX (s : ℝ) : HasDerivAt X (a*C s-b*S s) s :=
    ((((hx.differentiable (by simp) s).hasDerivAt).const_mul a).sub (((hy.differentiable (by simp) s).hasDerivAt).const_mul b)).add_const u
  have dY (s : ℝ) : HasDerivAt Y (b*C s+a*S s) s :=
    ((((hx.differentiable (by simp) s).hasDerivAt).const_mul b).add (((hy.differentiable (by simp) s).hasDerivAt).const_mul a)).add_const v
  have dw (s : ℝ) : HasDerivAt w a s := by
    convert! (((dX s).mul (dC s)).add ((dY s).mul (dS s))) using 1
    have nn := normal s
    dsimp only [n] at nn
    linear_combination -a*unit s-k s*nn
  have dn (s : ℝ) : HasDerivAt n (b-k s*w s) s := by
    convert! ((((dX s).neg.mul (dS s)).add ((dY s).mul (dC s)))) using 1
    dsimp only [w,Pi.neg_apply]
    linear_combination -b*unit s
  have dlin (s : ℝ) : HasDerivAt (fun s => w s-a*s) 0 s := by
    convert! (dw s).sub ((hasDerivAt_id s).const_mul a) using 1
    ring
  have diff (s t : ℝ) : w s-a*s=w t-a*t :=
    is_const_of_deriv_eq_zero (fun x => (dlin x).differentiableAt) (fun x => (dlin x).deriv) s t
  have per : w L=w 0 := by
    have px := px' 0
    have py := py' 0
    have pc : C (0+L)=C 0 := (SolitonClassification.Rotating.NormalEvolution.periodic_deriv px') 0
    have ps : S (0+L)=S 0 := (SolitonClassification.Rotating.NormalEvolution.periodic_deriv py') 0
    simp only [zero_add] at px py pc ps
    simp only [w,X,Y,px,py,pc,ps]
  have d := diff L 0
  rw [per,mul_zero,sub_zero] at d
  have a0 : a=0 := (mul_eq_zero.mp (by linarith : a*L=0)).resolve_right hL.ne'
  have wconst (s : ℝ) : w s=w 0 := by simpa only [a0,zero_mul,sub_zero] using diff s 0
  have zeroN : n=fun _ => 0 := funext normal
  have eq (s : ℝ) : b=k s*w 0 := by
    have hn := (dn s).deriv
    rw [zeroN,deriv_const',wconst] at hn
    linarith
  obtain ⟨p,q,diffK⟩ := different
  have hprod : (k p-k q)*w 0=0 := by linear_combination eq q - eq p
  have w0 := (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr diffK)
  have b0 : b=0 := by simpa only [w0,mul_zero] using eq 0
  have hn := normal 0
  dsimp only [n,X,Y] at hn
  dsimp only [w,X,Y] at w0
  simp only [a0,b0,zero_mul,sub_zero,zero_add,add_zero] at hn w0
  refine ⟨a0,b0,?_,?_⟩
  · linear_combination (C 0)*w0-(S 0)*hn-u*unit 0
  · linear_combination (S 0)*w0+(C 0)*hn-v*unit 0

end
end ClosedSimilarity
#print axioms ClosedSimilarity.tangent_similarity_zero
