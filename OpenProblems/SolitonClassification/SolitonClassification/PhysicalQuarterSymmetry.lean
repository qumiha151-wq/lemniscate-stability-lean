import SolitonClassification.PhysicalSeamCrossing

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace ClosedSimilarity.CrossingFrame
open ReflectedArc

private def supportOf (f : ℝ → State) (s : ℝ) : Support := ![f s 0,f s 1,f s 2,f s 3]

private theorem support_solves {f : ℝ → State} (df : ∀s, HasDerivAt f (field (f s)) s) :
    ReflectedMarker.Solves (supportOf f) := by
  intro s
  have d := hasDerivAt_pi.mp (df s)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact d 0
  · exact d 1
  · exact d 2
  · exact d 3

private theorem angle_eq {f g : ℝ → State} (df : ∀s, HasDerivAt f (field (f s)) s)
    (dg : ∀s, HasDerivAt g (field (g s)) s) (start : f 0=g 0) (s : ℝ) : f s 4=g s 4 := by
  have eq := ReflectedMarker.support_unique (support_solves df) (support_solves dg) (a:=0)
    (by simp [supportOf,start])
  have k (x : ℝ) : f x 0=g x 0 := congrFun (congrFun eq x) 0
  have d₁ (x) : HasDerivAt (fun t => f t 4) (f x 0) x := hasDerivAt_pi.mp (df x) 4
  have d₂ (x) : HasDerivAt (fun t => g t 4) (f x 0) x := k x ▸ hasDerivAt_pi.mp (dg x) 4
  exact congrFun (equal_primitives d₁ d₂ (congrFun start 4)) s

private theorem odd_of_even_velocity {f : ℝ → ℝ} (df : Differentiable ℝ f) (start : f 0=0)
    (even : ∀s, deriv f (-s)=deriv f s) (s : ℝ) : f (-s)= -f s := by
  have d (t : ℝ) : HasDerivAt (fun x => -f (-x)) (deriv f t) t := by
    convert! ((df (-t)).hasDerivAt.comp t (hasDerivAt_id t).neg).neg using 1
    simp [even]
  have eq := congrFun (equal_primitives d (fun t => (df t).hasDerivAt) (by simp [start])) s
  change -f (-s)=f s at eq
  linarith

/-- Central inversion of actual geometric position, in its original fixed
Cartesian axes. The initial position vanishes and the initial tangent is free. -/
theorem physical_odd {L b : ℝ} (P : ZeroTurnExpander L b) (pb : 0<b) (s : ℝ) :
    (P.X (-s),P.Y (-s)) = -(P.X s,P.Y s) := by
  let z := state P
  let f := fun t => atCenter (z (2*0-t))
  have df (t) : HasDerivAt f (field (f t)) t :=
    center_reverses z 0 t (state_solves P pb _)
  have start : f 0=z 0 := by
    ext i; fin_cases i <;> simp [f,z,state,addAngle,atCenter,P.cartesianSupport_zero]
  have even (t : ℝ) : turn b (-t)=turn b t := by
    simpa [f,z,state,addAngle,atCenter] using angle_eq df (state_solves P pb) start t
  have vel := (physical_position P pb).1
  have xeven (t) : deriv P.X (-t)=deriv P.X t := by rw [(vel (-t)).1,(vel t).1,even]
  have yeven (t) : deriv P.Y (-t)=deriv P.Y t := by rw [(vel (-t)).2,(vel t).2,even]
  exact Prod.ext (odd_of_even_velocity (P.X_smooth.differentiable (by simp)) P.center_crossing.1 xeven s)
    (odd_of_even_velocity (P.Y_smooth.differentiable (by simp)) P.center_crossing.2.1 yeven s)

private theorem rotation_respects_scalar {A B x y u v c : ℝ} (unit : A^2+B^2=1) :
    (A*x-B*y=c*(A*u-B*v) ∧ A*y+B*x=c*(A*v+B*u)) ↔ (x=c*u ∧ y=c*v) := by
  constructor
  · rintro ⟨h,k⟩
    constructor
    · linear_combination A*h+B*k-(x-c*u)*unit
    · linear_combination A*k-B*h-(y-c*v)*unit
  · rintro ⟨h,k⟩
    rw [h,k]; constructor <;> ring

/-- Fast and true geometric positions agree up to a fixed oriented rotation
and a positive scale. Testing equality, opposition or a scalar multiple
can be done entirely in fast coordinates. -/
theorem physical_fast_scalar_iff {L b : ℝ} (P : ZeroTurnExpander L b) (pb : 0<b) (t u c : ℝ) :
    (P.X t=c*P.X u ∧ P.Y t=c*P.Y u) ↔
      (CrossingResponse.X (rate b) (time b t)=c*CrossingResponse.X (rate b) (time b u) ∧
       CrossingResponse.Y (rate b) (time b t)=c*CrossingResponse.Y (rate b) (time b u)) := by
  have pos := (physical_position P pb).2
  rw [(pos t).1,(pos u).1,(pos t).2,(pos u).2,rotation_respects_scalar (P.unit_speed 0)]
  simp only [labX,labY,← mul_div_assoc,div_left_inj' (Real.sqrt_pos.mpr pb).ne']

/-- If the nonzero seam point and the selected point both have slope
β relative to the positive laboratory y-axis, the latter lies on the
true physical reflection axis. -/
theorem on_seam_axis_of_lab {L b S s β : ℝ} (P : ZeroTurnExpander L b) (pb : 0<b)
    (hq : P.cartesianSupport S 3=0) (seam : labX b S=β*labY b S)
    (nonzero : labY b S≠0) (target : labX b s=β*labY b s) :
    ReflectedCrossings.x (state P) S s=0 := by
  let C := Real.cos (turn b S)
  let D := Real.sin (turn b S)
  have xS : ReflectedCrossings.x (state P) S S=0 := by
    simp [ReflectedCrossings.x,ReflectedCrossings.angle,state,addAngle,hq]
  have line := (seam_coordinates P pb S S).1
  change ReflectedCrossings.x (state P) S S=C*labX b S+D*labY b S at line
  rw [xS,seam] at line
  have scale : C*β+D=0 :=
    (mul_eq_zero.mp (show (C*β+D)*labY b S=0 by linear_combination -line)).resolve_right nonzero
  rw [(seam_coordinates P pb S s).1,target]
  change C*(β*labY b s)+D*labY b s=0
  linear_combination labY b s*scale

private theorem physical_seam_iff {L b : ℝ} (P : ZeroTurnExpander L b) (pb : 0<b) (S t u c : ℝ) :
    (P.X t=c*P.X u ∧ P.Y t=c*P.Y u) ↔
      (ReflectedCrossings.x (state P) S t=c*ReflectedCrossings.x (state P) S u ∧
       ReflectedCrossings.y (state P) S t=c*ReflectedCrossings.y (state P) S u) := by
  have pos := (physical_position P pb).2
  have f (s : ℝ) := seam_coordinates P pb S s
  rw [(pos t).1,(pos u).1,(pos t).2,(pos u).2,(f t).1,(f u).1,(f t).2,(f u).2]
  rw [rotation_respects_scalar (P.unit_speed 0)]
  let A := Real.cos (turn b S)
  let B := Real.sin (turn b S)
  have unit : A^2+(-B)^2=1 := by simp [A,B]
  have h := rotation_respects_scalar (x:=labX b t) (y:=labY b t) (u:=labX b u) (v:=labY b u) (c:=c) unit
  simpa only [A,B,neg_mul,sub_eq_add_neg,neg_neg] using h.symm

/-- For a point on the seam axis, reflection of any physical label keeps
the property of attaining that point or any signed scalar multiple of it. -/
theorem reflected_hit_iff {L b S s : ℝ} (P : ZeroTurnExpander L b) (pb : 0<b)
    (hv : P.cartesianSupport S 1=0) (hq : P.cartesianSupport S 3=0)
    (onAxis : ReflectedCrossings.x (state P) S s=0) (c t : ℝ) :
    (P.X (2*S-t)=c*P.X s ∧ P.Y (2*S-t)=c*P.Y s) ↔
      (P.X t=c*P.X s ∧ P.Y t=c*P.Y s) := by
  rw [physical_seam_iff P pb S,physical_seam_iff P pb S]
  obtain ⟨x,y,_⟩ := ReflectedCrossings.seam_reflection (state_solves P pb) (S:=S) hv hq t
  rw [x,y,onAxis,mul_zero,neg_eq_zero]

end ClosedSimilarity.CrossingFrame
#print axioms ClosedSimilarity.CrossingFrame.physical_odd
#print axioms ClosedSimilarity.CrossingFrame.physical_fast_scalar_iff
#print axioms ClosedSimilarity.CrossingFrame.on_seam_axis_of_lab
#print axioms ClosedSimilarity.CrossingFrame.reflected_hit_iff
