import Migration.ForceLobeCover
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Rotating.UnitLoop
variable {L : ℝ} (c : UnitLoop L)

private theorem unit_angle {x y : ℝ} (unit : x^2+y^2=1) :
    ∃u : ℝ, Real.cos u=x ∧ Real.sin u=y := by
  let z : ℂ := ⟨x,y⟩
  have nz : ‖z‖=1 := by
    rw [Complex.norm_def]; change Real.sqrt (x*x+y*y)=1
    rw [show x*x+y*y=1 by nlinarith only [unit]]; exact Real.sqrt_one
  exact ⟨z.arg,by rw [Complex.cos_arg (norm_ne_zero_iff.mp (by rw [nz]; norm_num)),nz,div_one],
    by rw [Complex.sin_arg,nz,div_one]⟩

theorem tangent_phase : ∃ θ : ℝ→ℝ, (∀s, HasDerivAt θ (c.k s) s) ∧
    ∀s, Real.cos (θ s)=deriv c.x s ∧ Real.sin (θ s)=deriv c.y s := by
  obtain ⟨a,ca,sa⟩ := unit_angle (c.unit 0)
  let θ := fun s => a+∫t in (0:ℝ)..s,c.k t
  have d (s : ℝ) : HasDerivAt θ (c.k s) s := by
    exact (intervalIntegral.integral_hasDerivAt_right (c.contK.intervalIntegrable 0 s)
      c.contK.aestronglyMeasurable.stronglyMeasurableAtFilter c.contK.continuousAt).const_add a
  let P := fun s => (Real.cos (θ s)-deriv c.x s)^2+(Real.sin (θ s)-deriv c.y s)^2
  have x (s) : HasDerivAt (deriv c.x) (-c.k s*deriv c.y s) s := by
    rw [← frenet_x c.hx c.hy c.unit s]
    exact ((contDiff_infty_iff_deriv.mp c.hx).2.differentiable (by simp) s).hasDerivAt
  have y (s) : HasDerivAt (deriv c.y) (c.k s*deriv c.x s) s := by
    rw [← frenet_y c.hx c.hy c.unit s]
    exact ((contDiff_infty_iff_deriv.mp c.hy).2.differentiable (by simp) s).hasDerivAt
  have dp (s) : HasDerivAt P 0 s := by
    apply ((((d s).cos.sub (x s)).pow 2).add (((d s).sin.sub (y s)).pow 2)).congr_deriv
    dsimp; ring
  have zero : P 0=0 := by simp [P,θ,ca,sa]
  refine ⟨θ,d,?_⟩
  intro s
  have eq := is_const_of_deriv_eq_zero (fun r=>(dp r).differentiableAt) (fun r=>(dp r).deriv) s 0
  rw [zero] at eq; dsimp only [P] at eq
  constructor <;> nlinarith [sq_nonneg (Real.cos (θ s)-deriv c.x s),sq_nonneg (Real.sin (θ s)-deriv c.y s)]

theorem every_normal_of_full_turn {s t : ℝ} (st : s≤t)
    (turn : 2*Real.pi≤|∫v in s..t,c.k v|) {U V : ℝ} (unit : U^2+V^2=1) :
    ∃u∈Icc s t, -deriv c.y u=U ∧ deriv c.x u=V := by
  obtain ⟨θ,d,phase⟩ := c.tangent_phase
  obtain ⟨v,cv,sv⟩ := unit_angle (x:=V) (y:=-U) (by nlinarith only [unit])
  let C := fun s : ℝ => (Real.cos s,Real.sin s)
  have per : Function.Periodic C (2*Real.pi) := fun x => by simp [C]
  have ct : Continuous θ := continuous_iff_continuousAt.mpr fun x=>(d x).continuousAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _=>d v) (c.contK.intervalIntegrable ..)] at turn
  have hit : ∃u∈Icc s t,C (θ u)=C v := by
    rcases le_abs.mp turn with pos|neg
    · obtain ⟨w,hw,ew⟩ := per.exists_mem_Ico (by positivity) v (θ s)
      obtain ⟨u,hu,eu⟩ := intermediate_value_Icc st ct.continuousOn
        (show w∈Icc (θ s) (θ t) from ⟨hw.1,by linarith only [hw.2,pos]⟩)
      exact ⟨u,hu,eu ▸ ew.symm⟩
    · obtain ⟨w,hw,ew⟩ := per.exists_mem_Ico (by positivity) v (θ t)
      obtain ⟨u,hu,eu⟩ := intermediate_value_Icc' st ct.continuousOn
        (show w∈Icc (θ t) (θ s) from ⟨hw.1,by linarith only [hw.2,neg]⟩)
      exact ⟨u,hu,eu ▸ ew.symm⟩
  obtain ⟨u,hu,eq⟩ := hit
  have dx := congrArg Prod.fst eq
  have dy := congrArg Prod.snd eq
  change Real.cos (θ u)=Real.cos v at dx
  change Real.sin (θ u)=Real.sin v at dy
  rw [(phase u).1,cv] at dx
  rw [(phase u).2,sv] at dy
  exact ⟨u,hu,by linarith only [dy],dx⟩

/-- A sign-definite force arc accumulating one complete tangent turn prevents
whole-curve migration for the entire similarity motion, at any total turning. -/
theorem centered_disk_of_one_force_arc {a b f r s t : ℝ} (ap : 0<a) (lp : 0<L)
    (sol : c.IsRotating a b) (st : s≤t) (turn : 2*Real.pi≤|∫v in s..t,c.k v|)
    (side : (∀u∈Icc s t,f≤c.F u) ∨ (∀u∈Icc s t,c.F u≤ -f))
    (margin : a*Real.sqrt (1+b^2)*r≤f) :
    Metric.closedBall (0:ℂ) r ⊆ convexHull ℝ c.traceSet := by
  apply c.centered_disk_of_signed_force_cover ap lp sol _ margin
  intro U V unit
  rcases side with pos|neg
  · obtain ⟨u,hu,nx,ny⟩ := c.every_normal_of_full_turn st turn unit
    exact Or.inl ⟨u,nx,ny,pos u hu⟩
  · obtain ⟨u,hu,nx,ny⟩ := c.every_normal_of_full_turn st turn (U:=-U) (V:=-V) (by simpa only [neg_sq] using unit)
    exact Or.inr ⟨u,nx,ny,neg u hu⟩

end MigrationGeometry.Rotating.UnitLoop

#print axioms MigrationGeometry.Rotating.UnitLoop.centered_disk_of_one_force_arc
