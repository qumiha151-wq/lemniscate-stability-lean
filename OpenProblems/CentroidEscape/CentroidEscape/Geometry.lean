import CentroidEscape.PeriodicOrbit
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Euclidean geometry of the periodic expander state

All planar vectors below belong to EuclideanSpace R (Fin 2), with its
Euclidean norm and inner product. The geometric derivative identities are
derived from the actual six-coordinate ODE, not supplied as assumptions.
-/

namespace CentroidEscape

noncomputable section

set_option backward.isDefEq.respectTransparency false

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def planePair (x y : ℝ) : Plane := !₂[x,y]
def position (z : State) : Plane := planePair (z 0) (z 1)
def tangent (z : State) : Plane := planePair (z 2) (z 3)
def normal (z : State) : Plane := planePair (-z 3) (z 2)

lemma planePair_derivative {x y : ℝ → ℝ} {x' y' t : ℝ}
    (hx : HasDerivAt x x' t) (hy : HasDerivAt y y' t) :
    HasDerivAt (fun s => planePair (x s) (y s)) (planePair x' y') t := by
  have hp : HasDerivAt (fun s => ![x s, y s]) ![x',y'] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact hx
    · exact hy
  exact (PiLp.hasFDerivAt_toLp 2 ![x t,y t]).comp_hasDerivAt t hp

lemma position_derivative {q : ℝ → State} {s : ℝ}
    (hq : HasDerivAt q (field (q s)) s) :
    HasDerivAt (fun r => position (q r)) (tangent (q s)) s := by
  rw [hasDerivAt_pi] at hq
  simpa [position, tangent, field] using planePair_derivative (hq 0) (hq 1)

lemma tangent_derivative {q : ℝ → State} {s : ℝ}
    (hq : HasDerivAt q (field (q s)) s) :
    HasDerivAt (fun r => tangent (q r)) ((q s 4) • normal (q s)) s := by
  rw [hasDerivAt_pi] at hq
  convert! planePair_derivative (hq 2) (hq 3) using 1
  ext i
  fin_cases i <;> simp [normal, planePair, field]

lemma normal_derivative {q : ℝ → State} {s : ℝ}
    (hq : HasDerivAt q (field (q s)) s) :
    HasDerivAt (fun r => normal (q r)) (-(q s 4) • tangent (q s)) s := by
  rw [hasDerivAt_pi] at hq
  convert! planePair_derivative (hq 3).neg (hq 2) using 1
  ext i
  fin_cases i <;> simp [tangent, planePair, field]

lemma tangent_norm_sq (z : State) : ‖tangent z‖^2 = tangentSquare z := by
  simp [EuclideanSpace.real_norm_sq_eq, tangent, tangentSquare, planePair, Fin.sum_univ_two]

lemma normal_norm_sq (z : State) : ‖normal z‖^2 = tangentSquare z := by
  simp [EuclideanSpace.real_norm_sq_eq, normal, tangentSquare, planePair, Fin.sum_univ_two]
  ring

lemma tangent_normal_inner (z : State) : inner ℝ (tangent z) (normal z) = 0 := by
  simp [tangent, normal, planePair, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_two]
  ring

lemma position_normal_inner (z : State) :
    inner ℝ (position z) (normal z) = -(z 0 * z 3) + z 1 * z 2 := by
  simp [position, normal, planePair, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_two]
  ring

lemma tangent_norm_one {z : State} (hu : tangentSquare z = 1) : ‖tangent z‖ = 1 := by
  have hsq := tangent_norm_sq z
  have hn := norm_nonneg (tangent z)
  nlinarith

lemma normal_norm_one {z : State} (hu : tangentSquare z = 1) : ‖normal z‖ = 1 := by
  have hsq := normal_norm_sq z
  have hn := norm_nonneg (normal z)
  nlinarith

theorem position_unit_speed {q : ℝ → State} {s : ℝ}
    (hq : HasDerivAt q (field (q s)) s) (hu : tangentSquare (q s) = 1) :
    ‖deriv (fun r => position (q r)) s‖ = 1 := by
  rw [(position_derivative hq).deriv]
  exact tangent_norm_one hu

theorem position_immersed {q : ℝ → State} {s : ℝ}
    (hq : HasDerivAt q (field (q s)) s) (hu : tangentSquare (q s) = 1) :
    deriv (fun r => position (q r)) s ≠ 0 := by
  intro hzero
  have := position_unit_speed hq hu
  simp [hzero] at this

lemma curvature_derivative {q : ℝ → State} {s : ℝ}
    (hq : HasDerivAt q (field (q s)) s) :
    HasDerivAt (fun r => q r 4) (q s 5) s := by
  simpa [field] using hasDerivAt_pi.mp hq 4

lemma curvature_second_derivative {q : ℝ → State}
    (hq : ∀ s, HasDerivAt q (field (q s)) s) (s : ℝ) :
    deriv (deriv (fun r => q r 4)) s =
      -(q s 4)^3/2 + q s 0*q s 3 - q s 1*q s 2 := by
  have hd : deriv (fun r => q r 4) = fun r => q r 5 := by
    funext r
    exact (curvature_derivative (hq r)).deriv
  rw [hd]
  simpa [field] using (hasDerivAt_pi.mp (hq s) 5).deriv

theorem signed_curvature {q : ℝ → State} {s : ℝ}
    (hq : HasDerivAt q (field (q s)) s) (hu : tangentSquare (q s) = 1) :
    inner ℝ (deriv (fun r => tangent (q r)) s) (normal (q s)) = q s 4 := by
  rw [(tangent_derivative hq).deriv, real_inner_smul_left,
    real_inner_self_eq_norm_sq, normal_norm_one hu]
  simp

/-- The actual arclength curvature satisfies the normalized expander equation. -/
theorem profile_expander_equation {q : ℝ → State}
    (hq : ∀ s, HasDerivAt q (field (q s)) s) (s : ℝ) :
    deriv (deriv (fun r => q r 4)) s + (q s 4)^3/2 =
      -inner ℝ (position (q s)) (normal (q s)) := by
  rw [curvature_second_derivative hq, position_normal_inner]
  ring

/-- Spatial dilation expressed in its own arclength coordinate. -/
def scaledProfile (q : ℝ → State) (R a : ℝ) : Plane := R • position (q (a/R))

lemma scaledProfile_derivative {q : ℝ → State} (hq : ∀ s, HasDerivAt q (field (q s)) s)
    {R a : ℝ} (hR : R ≠ 0) :
    HasDerivAt (scaledProfile q R) (tangent (q (a/R))) a := by
  have hc : HasDerivAt (fun r : ℝ => r/R) (1/R) a := (hasDerivAt_id a).div_const R
  have hh := ((position_derivative (hq (a/R))).scomp a hc).const_smul R
  convert! hh using 1
  rw [smul_smul]
  simp [hR]

theorem scaledProfile_unit_speed {q : ℝ → State}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hu : ∀ s, tangentSquare (q s) = 1) {R a : ℝ} (hR : R ≠ 0) :
    ‖deriv (scaledProfile q R) a‖ = 1 := by
  rw [(scaledProfile_derivative hq hR).deriv]
  exact tangent_norm_one (hu _)

/-- Curvature of the dilated profile, using its own arclength variable. -/
def scaledCurvature (q : ℝ → State) (R a : ℝ) : ℝ := q (a/R) 4 / R

lemma scaledCurvature_derivative {q : ℝ → State}
    (hq : ∀ s, HasDerivAt q (field (q s)) s) (R a : ℝ) :
    HasDerivAt (scaledCurvature q R) (q (a/R) 5 / R^2) a := by
  have hc := (hasDerivAt_id a).div_const R
  have hh := ((curvature_derivative (hq (a/R))).comp a hc).div_const R
  convert! hh using 1
  ring

lemma scaledCurvature_second_derivative {q : ℝ → State}
    (hq : ∀ s, HasDerivAt q (field (q s)) s) (R a : ℝ) :
    deriv (deriv (scaledCurvature q R)) a =
      (-(q (a/R) 4)^3/2 + q (a/R) 0*q (a/R) 3 -
        q (a/R) 1*q (a/R) 2) / R^3 := by
  have hd : deriv (scaledCurvature q R) = fun b => q (b/R) 5 / R^2 := by
    funext b
    exact (scaledCurvature_derivative hq R b).deriv
  rw [hd]
  have hc := (hasDerivAt_id a).div_const R
  have hh := ((hasDerivAt_pi.mp (hq (a/R)) 5).comp a hc).div_const (R^2)
  convert! hh.deriv using 1
  dsimp [field]
  ring

lemma scaled_tangent_derivative {q : ℝ → State}
    (hq : ∀ s, HasDerivAt q (field (q s)) s) (R a : ℝ) :
    HasDerivAt (fun b => tangent (q (b/R)))
      (scaledCurvature q R a • normal (q (a/R))) a := by
  have hh := (tangent_derivative (hq (a/R))).scomp a ((hasDerivAt_id a).div_const R)
  convert! hh using 1
  rw [smul_smul]
  congr 1
  dsimp [scaledCurvature]
  ring

theorem scaled_signed_curvature {q : ℝ → State}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hu : ∀ s, tangentSquare (q s) = 1) (R a : ℝ) :
    inner ℝ (deriv (fun b => tangent (q (b/R))) a) (normal (q (a/R))) =
      scaledCurvature q R a := by
  rw [(scaled_tangent_derivative hq R a).deriv, real_inner_smul_left,
    real_inner_self_eq_norm_sq, normal_norm_one (hu _)]
  simp

/-- The force is computed from derivatives in the scaled arclength coordinate. -/
def scaledForce (q : ℝ → State) (R a : ℝ) : ℝ :=
  deriv (deriv (scaledCurvature q R)) a + (scaledCurvature q R a)^3/2

theorem scaledForce_eq {q : ℝ → State}
    (hq : ∀ s, HasDerivAt q (field (q s)) s) (R a : ℝ) :
    scaledForce q R a = -inner ℝ (position (q (a/R))) (normal (q (a/R))) / R^3 := by
  rw [scaledForce, scaledCurvature_second_derivative hq, position_normal_inner]
  dsimp [scaledCurvature]
  ring

/-- The usual expander radius. Its formula is established, not assumed. -/
def expanderRadius (t : ℝ) : ℝ := (1 + 4*t) ^ (1/4 : ℝ)

lemma expanderRadius_pos {t : ℝ} (ht : 0 ≤ t) : 0 < expanderRadius t := by
  exact Real.rpow_pos_of_pos (by linarith) _

lemma expanderRadius_derivative {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt expanderRadius (1 / (expanderRadius t)^3) t := by
  have hx : 0 < 1 + 4*t := by linarith
  have hd : HasDerivAt (fun s : ℝ => 1 + 4*s) 4 t := by
    convert! ((hasDerivAt_id t).const_mul 4).const_add 1 using 1
    ring
  have hh := hd.rpow_const (p := (1/4 : ℝ)) (Or.inl hx.ne')
  have he : (4 : ℝ) * (1/4) * (1+4*t)^((1/4 : ℝ)-1) =
      1 / (expanderRadius t)^3 := by
    rw [expanderRadius, ← Real.rpow_mul_natCast hx.le]
    norm_num
    exact Real.rpow_neg hx.le _
  exact he ▸ hh

/-- The homothetic family uses the original profile parameter s. -/
def expandingCurve (q : ℝ → State) (t s : ℝ) : Plane :=
  expanderRadius t • position (q s)

lemma expandingCurve_space_derivative {q : ℝ → State}
    (hq : ∀ s, HasDerivAt q (field (q s)) s) (t s : ℝ) :
    HasDerivAt (expandingCurve q t) (expanderRadius t • tangent (q s)) s := by
  exact (position_derivative (hq s)).const_smul (expanderRadius t)

/-- Speed in the original profile parameter, used for arclength integrals. -/
theorem expandingCurve_speed {q : ℝ → State}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hu : ∀ s, tangentSquare (q s) = 1) {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    ‖deriv (expandingCurve q t) s‖ = expanderRadius t := by
  rw [(expandingCurve_space_derivative hq t s).deriv, norm_smul,
    tangent_norm_one (hu s), Real.norm_eq_abs, abs_of_pos (expanderRadius_pos ht), mul_one]

lemma expandingCurve_time_derivative (q : ℝ → State) {t : ℝ}
    (ht : 0 ≤ t) (s : ℝ) :
    HasDerivAt (fun r => expandingCurve q r s)
      ((1/(expanderRadius t)^3) • position (q s)) t := by
  exact (expanderRadius_derivative ht).smul_const _

/-- Actual scalar normal-velocity equation of free elastic flow. The curve
has an additional tangential velocity; removing it requires reparametrization. -/
theorem expandingCurve_normal_FEF {q : ℝ → State}
    (hq : ∀ s, HasDerivAt q (field (q s)) s) {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    inner ℝ (deriv (fun r => expandingCurve q r s) t) (normal (q s)) =
      -scaledForce q (expanderRadius t) (expanderRadius t * s) := by
  have hR := (expanderRadius_pos ht).ne'
  rw [(expandingCurve_time_derivative q ht s).deriv, real_inner_smul_left,
    scaledForce_eq hq]
  simp only [mul_div_cancel_left₀ s hR]
  ring

/-- Geometry is periodic whenever the underlying state is periodic. -/
theorem expandingCurve_periodic {q : ℝ → State} {P : ℝ}
    (hperiod : Function.Periodic q P) (t : ℝ) :
    Function.Periodic (expandingCurve q t) P := by
  intro s
  simp only [expandingCurve, hperiod s]

/-- A unit tangent and its quarter-turn form an orthonormal frame. -/
lemma plane_decomposition (v : Plane) {z : State} (hu : tangentSquare z = 1) :
    v = (inner ℝ v (tangent z)) • tangent z + (inner ℝ v (normal z)) • normal z := by
  have hs : z 2 ^ 2 + z 3 ^ 2 = 1 := hu
  ext i
  fin_cases i <;>
    simp [tangent, normal, planePair, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_two] <;>
    nlinarith [congrArg (fun x : ℝ => x * v 0) hs,
      congrArg (fun x : ℝ => x * v 1) hs]

/-- Subtracting the tangent component gives exactly the vector FEF velocity. -/
theorem expandingCurve_vector_FEF_mod_tangent {q : ℝ → State}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hu : ∀ s, tangentSquare (q s) = 1) {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    let V := deriv (fun r => expandingCurve q r s) t
    V - (inner ℝ V (tangent (q s))) • tangent (q s) =
      (-scaledForce q (expanderRadius t) (expanderRadius t * s)) • normal (q s) := by
  dsimp
  have hd := plane_decomposition (deriv (fun r => expandingCurve q r s) t) (hu s)
  rw [expandingCurve_normal_FEF hq ht s] at hd
  exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hd)

end
end CentroidEscape

#print axioms CentroidEscape.profile_expander_equation
#print axioms CentroidEscape.position_unit_speed

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Centroid geometry audit passed for {checked} declarations."
