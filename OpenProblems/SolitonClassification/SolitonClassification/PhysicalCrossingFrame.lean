import SolitonClassification.PhysicalCrossingResponse
import SolitonClassification.ReflectedCrossings

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace ClosedSimilarity.CrossingFrame
open CrossingResponse ReflectedArc

def rate (b : ℝ) := (b^2)⁻¹
def time (b s : ℝ) := Real.sqrt b*s
def turn (b s : ℝ) := angle (rate b) (time b s)
def labX (b s : ℝ) := X (rate b) (time b s)/Real.sqrt b
def labY (b s : ℝ) := Y (rate b) (time b s)/Real.sqrt b

private theorem primitive_d (f : ℝ → ℝ → ℝ)
    (c : Continuous (fun z : ℝ × ℝ => f z.1 z.2)) (e t : ℝ) :
    HasDerivAt (fun x => ∫ u in (0:ℝ)..x, f e u) (f e t) t := by
  have cf : Continuous (f e) := c.comp (show Continuous (fun x : ℝ => (e,x)) from
    continuous_const.prodMk continuous_id)
  exact intervalIntegral.integral_hasDerivAt_right (cf.intervalIntegrable 0 t)
    cf.aestronglyMeasurable.stronglyMeasurableAtFilter cf.continuousAt

private theorem dtime (b s : ℝ) : HasDerivAt (time b) (Real.sqrt b) s := by
  convert! (hasDerivAt_id s).const_mul (Real.sqrt b) using 1
  simp

theorem turn_derivative {L b : ℝ} (P : ZeroTurnExpander L b) (positive : 0<b) (s : ℝ) :
    HasDerivAt (turn b) (P.k s) s := by
  have c : Continuous (fun z : ℝ × ℝ => K z.1 z.2) := by
    have h : Continuous (fun z : ℝ × ℝ => (z.2,(z.1,(![0,1,0,0] : GlobalSupport.Phase)))) :=
      continuous_snd.prodMk (continuous_fst.prodMk continuous_const)
    exact (continuous_apply 0).comp (GlobalSupport.continuous_solution.comp h)
  have da : HasDerivAt (angle (rate b)) (K (rate b) (time b s)) (time b s) := primitive_d K c _ _
  have eq := congrFun (physical_fast_support P positive (time b s)) 0
  have sq := (Real.sqrt_pos.mpr positive).ne'
  rw [show time b s / Real.sqrt b = s by unfold time; field_simp] at eq
  change P.k s = Real.sqrt b*K (rate b) (time b s) at eq
  convert! da.comp s (dtime b s) using 1
  rw [eq]; ring

theorem lab_derivatives {b : ℝ} (positive : 0<b) (s : ℝ) :
    HasDerivAt (labX b) (Real.cos (turn b s)) s ∧ HasDerivAt (labY b) (Real.sin (turn b s)) s := by
  have sq := (Real.sqrt_pos.mpr positive).ne'
  have dx : HasDerivAt (X (rate b)) (tx (rate b) (time b s)) (time b s) := primitive_d tx tx_cont _ _
  have dy : HasDerivAt (Y (rate b)) (ty (rate b) (time b s)) (time b s) := primitive_d ty ty_cont _ _
  constructor
  · convert! ((dx.comp s (dtime b s)).div_const (Real.sqrt b)) using 1
    simp [turn,tx,sq]
  · convert! ((dy.comp s (dtime b s)).div_const (Real.sqrt b)) using 1
    simp [turn,ty,sq]

theorem equal_primitives {f g v : ℝ → ℝ} (df : ∀ s, HasDerivAt f (v s) s) (dg : ∀ s, HasDerivAt g (v s) s)
    (start : f 0=g 0) : f=g := by
  have d (s : ℝ) : HasDerivAt (fun t => f t-g t) 0 s := by
    convert! (df s).sub (dg s) using 1
    simp
  funext s
  have eq := is_const_of_deriv_eq_zero (fun t => (d t).differentiableAt) (fun t => (d t).deriv) s 0
  change f s-g s=f 0-g 0 at eq
  linarith

private theorem same_frenet {u v U V k : ℝ → ℝ} (du : ∀s, HasDerivAt u (-k s*v s) s)
    (dv : ∀s, HasDerivAt v (k s*u s) s) (dU : ∀s, HasDerivAt U (-k s*V s) s)
    (dV : ∀s, HasDerivAt V (k s*U s) s) (i : u 0=U 0) (j : v 0=V 0) (s : ℝ) : u s=U s ∧ v s=V s := by
  let E (t : ℝ) := (u t-U t)^2+(v t-V t)^2
  have d (t : ℝ) : HasDerivAt E 0 t := by
    convert! (((du t).sub (dU t)).pow 2).add (((dv t).sub (dV t)).pow 2) using 1
    simp only [Pi.sub_apply]
    ring
  have eq := is_const_of_deriv_eq_zero (fun t => (d t).differentiableAt) (fun t => (d t).deriv) s 0
  simp [E,i,j] at eq
  constructor <;> nlinarith [sq_nonneg (u s-U s),sq_nonneg (v s-V s)]

private theorem frenet {L b : ℝ} (P : ZeroTurnExpander L b) (s : ℝ) :
    HasDerivAt (deriv P.X) (-P.k s*deriv P.Y s) s ∧ HasDerivAt (deriv P.Y) (P.k s*deriv P.X s) s := by
  have dx := ((contDiff_infty_iff_deriv.mp P.X_smooth).2.differentiable (by simp) s).hasDerivAt
  have dy := ((contDiff_infty_iff_deriv.mp P.Y_smooth).2.differentiable (by simp) s).hasDerivAt
  have norm := (dx.pow 2).add (dy.pow 2)
  change HasDerivAt (fun t => deriv P.X t^2+deriv P.Y t^2) _ s at norm
  rw [show (fun t => deriv P.X t^2+deriv P.Y t^2)=(fun _=>1) from funext P.unit_speed] at norm
  have dot := norm.unique (hasDerivAt_const s 1)
  simp only [Nat.cast_ofNat] at dot
  constructor
  · convert! dx using 1
    linear_combination deriv (deriv P.X) s * P.unit_speed s - deriv P.X s * dot / 2 + deriv P.Y s * P.curvature s
  · convert! dy using 1
    linear_combination deriv (deriv P.Y) s * P.unit_speed s - deriv P.Y s * dot / 2 - deriv P.X s * P.curvature s

theorem turn_zero (b : ℝ) : turn b 0=0 := by
  change (∫ t in (0:ℝ)..(Real.sqrt b*0), K (rate b) t)=0
  simp

theorem lab_zero (b : ℝ) : labX b 0=0 ∧ labY b 0=0 := by
  change (∫ t in (0:ℝ)..(Real.sqrt b*0), tx (rate b) t)/_ = 0 ∧
    (∫ t in (0:ℝ)..(Real.sqrt b*0), ty (rate b) t)/_ = 0
  simp

/-- The initial unit tangent of an arbitrary normalized geometric expander
rotates the fast laboratory coordinates into its actual Cartesian position. -/
theorem physical_position {L b : ℝ} (P : ZeroTurnExpander L b) (pb : 0<b) :
    let A := deriv P.X 0
    let B := deriv P.Y 0
    (∀s, deriv P.X s=A*Real.cos (turn b s)-B*Real.sin (turn b s) ∧
      deriv P.Y s=A*Real.sin (turn b s)+B*Real.cos (turn b s)) ∧
    (∀s, P.X s=A*labX b s-B*labY b s ∧ P.Y s=A*labY b s+B*labX b s) := by
  let A := deriv P.X 0
  let B := deriv P.Y 0
  let U := fun s => A*Real.cos (turn b s)-B*Real.sin (turn b s)
  let V := fun s => A*Real.sin (turn b s)+B*Real.cos (turn b s)
  have dU (s) : HasDerivAt U (-P.k s*V s) s := by
    have d := turn_derivative P pb s
    convert! (d.cos.const_mul A).sub (d.sin.const_mul B) using 1
    dsimp [V]; ring
  have dV (s) : HasDerivAt V (P.k s*U s) s := by
    have d := turn_derivative P pb s
    convert! (d.sin.const_mul A).add (d.cos.const_mul B) using 1
    dsimp [U]; ring
  have vel := same_frenet (fun s => (frenet P s).1) (fun s => (frenet P s).2) dU dV
      (by simp [U,A,turn_zero]) (by simp [V,B,turn_zero])
  refine ⟨vel,?_⟩
  have dx (s) : HasDerivAt P.X (U s) s := (vel s).1 ▸ (P.X_smooth.differentiable (by simp) s).hasDerivAt
  have dy (s) : HasDerivAt P.Y (V s) s := (vel s).2 ▸ (P.Y_smooth.differentiable (by simp) s).hasDerivAt
  have x := equal_primitives dx (fun s => (((lab_derivatives pb s).1).const_mul A).sub (((lab_derivatives pb s).2).const_mul B))
    (by simp [P.center_crossing.1,(lab_zero b).1,(lab_zero b).2])
  have y := equal_primitives dy (fun s => (((lab_derivatives pb s).2).const_mul A).add (((lab_derivatives pb s).1).const_mul B))
    (by simp [P.center_crossing.2.1,(lab_zero b).1,(lab_zero b).2])
  exact fun s => ⟨congrFun x s,congrFun y s⟩

end ClosedSimilarity.CrossingFrame
#print axioms ClosedSimilarity.CrossingFrame.physical_position
