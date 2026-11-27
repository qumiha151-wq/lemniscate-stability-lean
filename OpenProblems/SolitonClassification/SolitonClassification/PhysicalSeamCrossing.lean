import SolitonClassification.PhysicalCrossingFrame

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace ClosedSimilarity.CrossingFrame
open ReflectedArc CrossingResponse


def addAngle (q : Support) (θ : ℝ) : State := ![q 0,q 1,q 2,q 3,θ]

/-- The physical support lifted by the real tangent angle in its initial
tangent frame. The first four coordinates are those of the actual curve. -/
def state {L b : ℝ} (P : ZeroTurnExpander L b) (s : ℝ) : State :=
  addAngle (P.cartesianSupport s) (turn b s)

private theorem lift_solution {z : ℝ → Support} {θ : ℝ → ℝ} (s : ℝ)
    (dz : HasDerivAt z (supportField (z s)) s) (dθ : HasDerivAt θ (z s 0) s) :
    HasDerivAt (fun t => addAngle (z t) (θ t)) (field (addAngle (z s) (θ s))) s := by
  have h := hasDerivAt_pi.mp dz
  apply hasDerivAt_pi.mpr
  intro i; fin_cases i
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3
  · exact dθ

theorem state_solves {L b : ℝ} (P : ZeroTurnExpander L b) (pb : 0<b) (s : ℝ) :
    HasDerivAt (state P) (field (state P s)) s := by
  exact lift_solution (z:=P.cartesianSupport) (θ:=turn b) s (P.cartesianSupport_solves s) (turn_derivative P pb s)

/-- The seam frame follows from the physical state and is a fixed
rotation of the initial laboratory coordinates. -/
theorem seam_coordinates {L b : ℝ} (P : ZeroTurnExpander L b) (pb : 0<b) (S s : ℝ) :
    ReflectedCrossings.x (state P) S s = Real.cos (turn b S)*labX b s + Real.sin (turn b S)*labY b s ∧
    ReflectedCrossings.y (state P) S s = Real.cos (turn b S)*labY b s - Real.sin (turn b S)*labX b s := by
  let C := Real.cos (turn b S)
  let D := Real.sin (turn b S)
  let z := state P
  have dx (t) : HasDerivAt (fun t => C*labX b t + D*labY b t) (Real.cos (ReflectedCrossings.angle z S t)) t := by
    convert! (((lab_derivatives pb t).1).const_mul C).add (((lab_derivatives pb t).2).const_mul D) using 1
    change Real.cos (turn b t - turn b S) = _
    rw [Real.cos_sub]; dsimp [C,D]; ring
  have dy (t) : HasDerivAt (fun t => C*labY b t - D*labX b t) (Real.sin (ReflectedCrossings.angle z S t)) t := by
    convert! (((lab_derivatives pb t).2).const_mul C).sub (((lab_derivatives pb t).1).const_mul D) using 1
    change Real.sin (turn b t - turn b S) = _
    rw [Real.sin_sub]; dsimp [C,D]; ring
  have ex := equal_primitives (fun t => (ReflectedCrossings.position_derivatives S t (state_solves P pb)).1) dx
    (by simp [ReflectedCrossings.x,state,addAngle,P.cartesianSupport_zero,(lab_zero b).1,(lab_zero b).2])
  have ey := equal_primitives (fun t => (ReflectedCrossings.position_derivatives S t (state_solves P pb)).2) dy
    (by simp [ReflectedCrossings.y,state,addAngle,P.cartesianSupport_zero,(lab_zero b).1,(lab_zero b).2])
  exact ⟨congrFun ex s,congrFun ey s⟩

private theorem rotation_injective {C D x y u v : ℝ} (unit : C^2+D^2=1)
    (eqx : C*x+D*y=C*u+D*v) (eqy : C*y-D*x=C*v-D*u) : x=u ∧ y=v := by
  constructor
  · linear_combination C*eqx-D*eqy-(x-u)*unit
  · linear_combination D*eqx+C*eqy-(y-v)*unit

private theorem periodic_deriv {f : ℝ → ℝ} {d : ℝ} (per : Function.Periodic f d)
    (df : Differentiable ℝ f) : Function.Periodic (deriv f) d := by
  intro s
  have h := (df (s+d)).hasDerivAt.comp s ((hasDerivAt_id s).add_const d)
  change HasDerivAt (fun u => f (u+d)) _ s at h
  rw [show (fun u => f (u+d))=f from funext per] at h
  simpa using h.deriv.symm

private theorem in_period {f : ℝ → ℝ} {d : ℝ} (pos : 0<d) (per : Function.Periodic f d)
    (s : ℝ) : f (toIcoMod pos 0 s)=f s := by
  rw [← self_sub_toIcoDiv_zsmul pos 0 s]
  exact per.sub_zsmul_eq _

/-- A transverse fast-axis root gives two labels of the actual geometric
expander, with nonparallel actual Cartesian derivatives, in every positive
position period. The seam slope is read directly from laboratory position. -/
theorem transverse_in_every_physical_period {L b S s β d : ℝ} (P : ZeroTurnExpander L b)
    (pb : 0<b) (hv : P.cartesianSupport S 1=0) (hq : P.cartesianSupport S 3=0)
    (seam : labX b S=β*labY b S) (seam_nonzero : labY b S≠0)
    (onAxis : labX b s=β*labY b s)
    (incidence : (Real.cos (turn b s)-β*Real.sin (turn b s)) *
      (Real.sin (turn b s)+β*Real.cos (turn b s)) ≠ 0)
    (pd : 0<d) (px : Function.Periodic P.X d) (py : Function.Periodic P.Y d) :
    ∃ u∈Ico (0:ℝ) d, ∃ v∈Ico (0:ℝ) d, u≠v ∧
      P.X u=P.X s ∧ P.Y u=P.Y s ∧ P.X v=P.X s ∧ P.Y v=P.Y s ∧
      deriv P.X u*deriv P.Y v-deriv P.Y u*deriv P.X v≠0 := by
  let C := Real.cos (turn b S)
  let D := Real.sin (turn b S)
  have unit : C^2+D^2=1 := Real.cos_sq_add_sin_sq _
  have xS : ReflectedCrossings.x (state P) S S=0 := by simp [ReflectedCrossings.x,ReflectedCrossings.angle,state,addAngle,hq]
  have axisLine := (seam_coordinates P pb S S).1
  change ReflectedCrossings.x (state P) S S=C*labX b S+D*labY b S at axisLine
  rw [xS,seam] at axisLine
  have scale : C*β+D=0 := by
    apply (mul_eq_zero.mp (show (C*β+D)*labY b S=0 by linear_combination -axisLine)).resolve_right seam_nonzero
  have cn : C≠0 := by
    intro h
    have z : D=0 := by simpa [h] using scale
    rw [h,z] at unit
    norm_num at unit
  have Dval : D= -C*β := by linarith
  have cross : ReflectedCrossings.x (state P) S s=0 := by
    rw [(seam_coordinates P pb S s).1,onAxis]
    change C*(β*labY b s)+D*labY b s=0
    rw [Dval]; ring
  have inc : Real.cos (turn b s-turn b S)*Real.sin (turn b s-turn b S) ≠ 0 := by
    rw [Real.cos_sub,Real.sin_sub]
    change (Real.cos (turn b s)*C+Real.sin (turn b s)*D)*(Real.sin (turn b s)*C-Real.cos (turn b s)*D)≠0
    rw [Dval]
    convert! mul_ne_zero (mul_ne_zero cn cn) incidence using 1
    ring
  let b' := 2*S-s
  obtain ⟨sx,sy,ang⟩ := ReflectedCrossings.seam_reflection (state_solves P pb) (S:=S) hv hq s
  have ex : ReflectedCrossings.x (state P) S b'=ReflectedCrossings.x (state P) S s := by rw [sx,cross,neg_zero]
  have labs := rotation_injective unit
    (((seam_coordinates P pb S b').1.symm.trans ex).trans (seam_coordinates P pb S s).1)
    (((seam_coordinates P pb S b').2.symm.trans sy).trans (seam_coordinates P pb S s).2)
  obtain ⟨vel,pos⟩ := physical_position P pb
  have eqx : P.X b'=P.X s := by rw [(pos b').1,(pos s).1,labs.1,labs.2]
  have eqy : P.Y b'=P.Y s := by rw [(pos b').2,(pos s).2,labs.1,labs.2]
  change turn b b'-turn b S= -(turn b s-turn b S) at ang
  have anglediff : turn b b'-turn b s = -(turn b s-turn b S)-(turn b s-turn b S) := by linarith
  have sins : Real.sin (turn b b'-turn b s)≠0 := by
    rw [anglediff,Real.sin_sub,Real.sin_neg,Real.cos_neg]
    intro zero; apply inc; linarith only [zero, mul_comm (Real.cos (turn b s-turn b S)) (Real.sin (turn b s-turn b S))]
  have det : deriv P.X s*deriv P.Y b'-deriv P.Y s*deriv P.X b' ≠0 := by
    rw [(vel s).1,(vel s).2,(vel b').1,(vel b').2]
    convert! sins using 1
    rw [Real.sin_sub]
    linear_combination (Real.cos (turn b s)*Real.sin (turn b b')-Real.sin (turn b s)*Real.cos (turn b b'))*P.unit_speed 0
  have dx := periodic_deriv px (P.X_smooth.differentiable (by simp))
  have dy := periodic_deriv py (P.Y_smooth.differentiable (by simp))
  let u := toIcoMod pd 0 s
  let v := toIcoMod pd 0 b'
  have actual : deriv P.X u*deriv P.Y v-deriv P.Y u*deriv P.X v≠0 := by
    simpa only [u,v,in_period pd dx,in_period pd dy] using det
  refine ⟨u,toIcoMod_mem_Ico' pd _,v,toIcoMod_mem_Ico' pd _,?_,
    in_period pd px s,in_period pd py s,(in_period pd px b').trans eqx,(in_period pd py b').trans eqy,actual⟩
  intro same; apply actual
  rw [same]; ring

end ClosedSimilarity.CrossingFrame
#print axioms ClosedSimilarity.CrossingFrame.transverse_in_every_physical_period
