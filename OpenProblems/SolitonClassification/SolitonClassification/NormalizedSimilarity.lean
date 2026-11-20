import SolitonClassification.ReflectedGeometry

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace ClosedSimilarity.ReflectedArc

private theorem affine_d {a t s : ℝ} : HasDerivAt (fun u : ℝ => a*u+t) a s := by
  simpa using ((hasDerivAt_id s).const_mul a).add_const t

private theorem smooth_d {f : ℝ → ℝ} (h : ContDiff ℝ ∞ f) (s : ℝ) :
    HasDerivAt f (deriv f s) s := (h.differentiable (by simp) s).hasDerivAt

private theorem derivative_identity {f g : ℝ → ℝ} {u v s : ℝ} (h : ∀ x, f x=g x)
    (hf : HasDerivAt f u s) (hg : HasDerivAt g v s) : u=v := by
  rw [show f=g from funext h] at hf
  exact hf.unique hg

/-- A fixed affine radial vector field everywhere tangent to a regular
    curve of nonzero curvature somewhere must vanish identically. -/
theorem radial_tangency_rigidity {L b : ℝ} (P : ZeroTurnExpander L b) (hb : b≠0)
    (c u v : ℝ) (tangent : ∀ s, (c*P.X s+u)*deriv P.Y s-
      (c*P.Y s+v)*deriv P.X s=0) : c=0 ∧ u=0 ∧ v=0 := by
  obtain ⟨z,hz⟩ : ∃ z, P.k z≠0 := by
    by_contra! h
    have he : P.k=fun _ => 0 := funext h
    have h0 := P.center_crossing.2.2.2
    simp [he] at h0
    exact hb h0.symm
  have acc (s : ℝ) : (c*P.X s+u)*deriv (deriv P.Y) s-
      (c*P.Y s+v)*deriv (deriv P.X) s=0 := by
    have H := derivative_identity tangent
      (((((smooth_d P.X_smooth s).const_mul c).add_const u).mul
        (smooth_d (contDiff_infty_iff_deriv.mp P.Y_smooth).2 s)).sub
        ((((smooth_d P.Y_smooth s).const_mul c).add_const v).mul
        (smooth_d (contDiff_infty_iff_deriv.mp P.X_smooth).2 s))) (hasDerivAt_const s 0)
    linarith only [H]
  have vanish (s : ℝ) (hs : P.k s≠0) : (c*P.X s+u)=0 ∧ (c*P.Y s+v)=0 := by
    have hx : (c*P.X s+u)*P.k s=0 := by
      rw [← P.curvature]
      linear_combination deriv P.X s * acc s - deriv (deriv P.X) s * tangent s
    have hy : (c*P.Y s+v)*P.k s=0 := by
      rw [← P.curvature]
      linear_combination deriv P.Y s * acc s - deriv (deriv P.Y) s * tangent s
    exact ⟨(mul_eq_zero.mp hx).resolve_right hs, (mul_eq_zero.mp hy).resolve_right hs⟩
  have near := P.k_smooth.continuous.continuousAt.eventually_ne hz
  have dx := (((smooth_d P.X_smooth z).const_mul c).add_const u).congr_of_eventuallyEq
    (near.mono fun s hs => (vanish s hs).1.symm)
  have dy := (((smooth_d P.Y_smooth z).const_mul c).add_const v).congr_of_eventuallyEq
    (near.mono fun s hs => (vanish s hs).2.symm)
  have xz := dx.unique (hasDerivAt_const z 0)
  have yz := dy.unique (hasDerivAt_const z 0)
  have cz : c=0 := by
    by_contra hc
    have xx := (mul_eq_zero.mp xz).resolve_left hc
    have yy := (mul_eq_zero.mp yz).resolve_left hc
    simpa [xx,yy] using P.unit_speed z
  simpa [cz] using And.intro cz (vanish z hz)

/-- The universal arclength parametrizations agree after an affine parameter
    change and a plane similarity. The choice of periods plays no role. The
    determinant condition alone suffices once unit speed is imposed. -/
structure LiftedSimilarity {L b T d : ℝ} (P : ZeroTurnExpander L b)
    (Q : ZeroTurnExpander T d) where
  a : ℝ
  offset : ℝ
  m : ℝ
  n : ℝ
  p : ℝ
  q : ℝ
  x : ℝ
  y : ℝ
  regular : a≠0
  area : (m*q-n*p)^2=a^4
  first : ∀ s, Q.X (a*s+offset)=m*P.X s+n*P.Y s+x
  second : ∀ s, Q.Y (a*s+offset)=p*P.X s+q*P.Y s+y

namespace LiftedSimilarity
variable {L b T d : ℝ} {P : ZeroTurnExpander L b} {Q : ZeroTurnExpander T d}
  (S : LiftedSimilarity P Q)

private theorem pull_coordinate {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (m n x : ℝ) (h : ∀ s, F (S.a*s+S.offset)=m*P.X s+n*P.Y s+x) :
    (∀ s, deriv F (S.a*s+S.offset)*S.a=m*deriv P.X s+n*deriv P.Y s) ∧
    (∀ s, deriv (deriv F) (S.a*s+S.offset)*S.a^2=
      m*deriv (deriv P.X) s+n*deriv (deriv P.Y) s) := by
  have e (s : ℝ) := derivative_identity h ((smooth_d hF _).comp s affine_d)
    ((((smooth_d P.X_smooth s).const_mul m).add ((smooth_d P.Y_smooth s).const_mul n)).add_const x)
  refine ⟨e,fun s => ?_⟩
  have H := derivative_identity e
    ((((smooth_d (contDiff_infty_iff_deriv.mp hF).2 _).comp s affine_d).mul_const S.a))
    (((smooth_d (contDiff_infty_iff_deriv.mp P.X_smooth).2 s).const_mul m).add
     ((smooth_d (contDiff_infty_iff_deriv.mp P.Y_smooth).2 s).const_mul n))
  linarith only [H]

theorem pull_curvature (s : ℝ) : Q.k (S.a*s+S.offset)*S.a^3=(S.m*S.q-S.n*S.p)*P.k s := by
  obtain ⟨x1,x2⟩ := S.pull_coordinate Q.X_smooth S.m S.n S.x S.first
  obtain ⟨y1,y2⟩ := S.pull_coordinate Q.Y_smooth S.p S.q S.y S.second
  rw [← Q.curvature,← P.curvature]
  linear_combination
    deriv (deriv Q.Y) (S.a*s+S.offset)*S.a^2 * x1 s +
    (S.m*deriv P.X s+S.n*deriv P.Y s)* y2 s -
    deriv (deriv Q.X) (S.a*s+S.offset)*S.a^2 * y1 s -
    (S.p*deriv P.X s+S.q*deriv P.Y s)* x2 s

theorem pull_slope (s : ℝ) : deriv Q.k (S.a*s+S.offset)*S.a^4=
    (S.m*S.q-S.n*S.p)*deriv P.k s := by
  have H := derivative_identity S.pull_curvature
    (((smooth_d Q.k_smooth _).comp s affine_d).mul_const (S.a^3))
    ((smooth_d P.k_smooth s).const_mul (S.m*S.q-S.n*S.p))
  linarith only [H]

/-- For coefficient-one expanders both the length scale and the dilation
    centre are determined by the immersed curve. -/
theorem scale_and_centre (hb : b≠0) : S.a^4=1 ∧ S.x=0 ∧ S.y=0 := by
  let D := S.m*S.q-S.n*S.p
  have det : D^2=S.a^4 := S.area
  have dn : D≠0 := fun e => S.regular (pow_eq_zero_iff (by decide : 4≠0) |>.mp
    (by simpa [e] using det.symm))
  have kk (s : ℝ) : deriv (deriv Q.k) (S.a*s+S.offset)*S.a^5=D*deriv (deriv P.k) s := by
    have H := derivative_identity S.pull_slope
      (((smooth_d (contDiff_infty_iff_deriv.mp Q.k_smooth).2 _).comp s affine_d).mul_const (S.a^4))
      ((smooth_d (contDiff_infty_iff_deriv.mp P.k_smooth).2 s).const_mul D)
    change _ = D*_ at H
    linarith only [H]
  have cube (s : ℝ) : Q.k (S.a*s+S.offset)^3*S.a^5=D*P.k s^3 := by
    have H : (Q.k (S.a*s+S.offset)*S.a^3)^3=(D*P.k s)^3 :=
      congrArg (fun z : ℝ => z^3) (S.pull_curvature s)
    apply mul_right_cancel₀ (pow_ne_zero 4 S.regular)
    linear_combination H + D*P.k s^3*det
  obtain ⟨x1,_⟩ := S.pull_coordinate Q.X_smooth S.m S.n S.x S.first
  obtain ⟨y1,_⟩ := S.pull_coordinate Q.Y_smooth S.p S.q S.y S.second
  have tang (s : ℝ) :
      ((S.a^4-1)*D*P.X s+S.a^4*(S.x*S.q-S.y*S.n))*deriv P.Y s-
      ((S.a^4-1)*D*P.Y s+S.a^4*(S.y*S.m-S.x*S.p))*deriv P.X s=0 := by
    have rate := Q.dilation_equation (S.a*s+S.offset)
    rw [S.first,S.second] at rate
    linear_combination (norm := (dsimp [D]; ring))
      -(S.a^5)*rate + D*P.dilation_equation s + kk s + cube s / 2 -
      S.a^4*(S.m*P.X s+S.n*P.Y s+S.x)*y1 s +
      S.a^4*(S.p*P.X s+S.q*P.Y s+S.y)*x1 s
  obtain ⟨r,u,v⟩ := radial_tangency_rigidity P hb _ _ _ tang
  have a4 : S.a^4=1 := sub_eq_zero.mp ((mul_eq_zero.mp r).resolve_right dn)
  rw [a4,one_mul] at u v
  have xx : S.x*D=0 := by dsimp [D]; linear_combination S.m*u+S.n*v
  have yy : S.y*D=0 := by dsimp [D]; linear_combination S.p*u+S.q*v
  exact ⟨a4,(mul_eq_zero.mp xx).resolve_right dn,(mul_eq_zero.mp yy).resolve_right dn⟩

end LiftedSimilarity
end ClosedSimilarity.ReflectedArc
#print axioms ClosedSimilarity.ReflectedArc.LiftedSimilarity.scale_and_centre
