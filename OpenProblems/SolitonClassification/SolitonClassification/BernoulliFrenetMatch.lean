import SolitonClassification.BernoulliArcMatch

noncomputable section
open Complex
namespace ClosedSimilarity.BernoulliGeometry
set_option backward.isDefEq.respectTransparency false

def position (c : ClosedUnitFrenetCurve) (s : ℝ) : ℂ := (c.x s:ℂ)+(c.y s:ℂ)*I
def direction (c : ClosedUnitFrenetCurve) (s : ℝ) : ℂ := (c.tx s:ℂ)+(c.ty s:ℂ)*I

theorem dposition (c : ClosedUnitFrenetCurve) (s : ℝ) :
    HasDerivAt (position c) (direction c s) s :=
  (c.dx s).ofReal_comp.add ((c.dy s).ofReal_comp.mul_const I)

theorem ddirection (c : ClosedUnitFrenetCurve) (s : ℝ) :
    HasDerivAt (direction c) (I*(c.k s:ℂ)*direction c s) s := by
  convert! (c.dtx s).ofReal_comp.add ((c.dty s).ofReal_comp.mul_const I) using 1
  dsimp only [direction]
  push_cast
  linear_combination (c.k s:ℂ)*(c.ty s:ℂ)*I_sq

theorem direction_unit (c : ClosedUnitFrenetCurve) (s : ℝ) : ‖direction c s‖=1 := by
  have ns : Complex.normSq (direction c s)=1 := by
    simpa only [direction,Complex.normSq_add_mul_I] using c.unit s
  rw [←Complex.sq_norm] at ns
  nlinarith [norm_nonneg (direction c s)]

/-- Matching arclength curvature matches actual positions after one unit
complex rotation, one dilation, and a translation. -/
theorem frenet_match (c : ClosedUnitFrenetCurve) {d s₀ : ℝ}
    (curv : ∀t,d*c.k (s₀+d*t)=curvature (angle t)) :
    ∃R : ℂ,‖R‖=1 ∧ ∀u,position c (s₀+d*arc u)=position c s₀+(d:ℂ)*R*beta u := by
  let X (t : ℝ) := position c (s₀+d*t)
  let T (t : ℝ) := direction c (s₀+d*t)
  let P (t : ℝ) := beta (angle t)
  let V (t : ℝ) := tangent (angle t)
  have clk (t : ℝ) : HasDerivAt (fun u=>s₀+d*u) d t := by
    simpa using (((hasDerivAt_id t).const_mul d).const_add s₀)
  have dX (t : ℝ) : HasDerivAt X ((d:ℂ)*T t) t := by
    simpa only [Complex.real_smul] using! (dposition c _).scomp t (clk t)
  have dT (t : ℝ) : HasDerivAt T (I*(curvature (angle t):ℂ)*T t) t := by
    convert! (ddirection c _).scomp t (clk t) using 1
    rw [←curv]
    simp only [Complex.real_smul,Complex.ofReal_mul,T]
    ring
  have dP (t : ℝ) : HasDerivAt P (V t) t := canonical_dpos t
  have dV (t : ℝ) : HasDerivAt V (I*(curvature (angle t):ℂ)*V t) t := canonical_dtang t
  have vn (t : ℝ) : V t≠0 := by
    intro vz
    have n := tangent_unit (angle t)
    change ‖V t‖=1 at n
    simp [vz] at n
  have rot (t : ℝ) : HasDerivAt (fun u=>T u/V u) 0 t := by
    convert! (dT t).div (dV t) (vn t) using 1
    ring
  let R := T 0/V 0
  have re (t : ℝ) : T t=R*V t := (div_eq_iff (vn t)).mp
    (is_const_of_deriv_eq_zero (fun u=>(rot u).differentiableAt) (fun u=>(rot u).deriv) t 0)
  have mag : ‖R‖=1 := by simp only [R,T,V,norm_div,direction_unit,tangent_unit,div_one]
  have delta (t : ℝ) : HasDerivAt (fun u=>X u-(d:ℂ)*R*P u) 0 t := by
    convert! (dX t).sub ((dP t).const_mul ((d:ℂ)*R)) using 1
    rw [re]
    ring
  refine ⟨R,mag,fun u=>?_⟩
  have eq := is_const_of_deriv_eq_zero (fun u=>(delta u).differentiableAt)
    (fun u=>(delta u).deriv) (arc u) 0
  change X (arc u)-(d:ℂ)*R*P (arc u)=X 0-(d:ℂ)*R*P 0 at eq
  simp only [X,P,angle_arc,angle_zero,beta_zero,mul_zero,add_zero,sub_zero] at eq
  linear_combination eq

end ClosedSimilarity.BernoulliGeometry
