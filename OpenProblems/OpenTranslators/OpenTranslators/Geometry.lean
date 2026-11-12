import OpenTranslators.RegularizedGlobal
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Actual position reconstruction and the geometric normal-component translator
equation. Time translation is not asserted to be a pure-normal parametrization.
The metric is expressed in Euclidean coordinates, not the max norm on a product. -/

namespace OpenTranslator.TranslatorGeometry
noncomputable section
open MeasureTheory Set
open scoped ContDiff

def betaX (z : ℝ → TranslatorState) (s : ℝ) : ℝ := ∫ u in 0..s, Real.cos (z u 0)
def betaY (z : ℝ → TranslatorState) (s : ℝ) : ℝ := ∫ u in 0..s, Real.sin (z u 0)
def positionX (z : ℝ → TranslatorState) (t s : ℝ) : ℝ := betaX z s + t
def positionY (z : ℝ → TranslatorState) (_t s : ℝ) : ℝ := betaY z s

def speedSquared (x y : ℝ → ℝ) (s : ℝ) : ℝ := (deriv x s)^2 + (deriv y s)^2
def signedCurvature (x y : ℝ → ℝ) (s : ℝ) : ℝ :=
  deriv x s * deriv (deriv y) s - deriv y s * deriv (deriv x) s
def elasticForce (x y : ℝ → ℝ) (s : ℝ) : ℝ :=
  deriv (deriv (signedCurvature x y)) s + (signedCurvature x y s)^3/2
def normalX (_x y : ℝ → ℝ) (s : ℝ) : ℝ := -deriv y s
def normalY (x _y : ℝ → ℝ) (s : ℝ) : ℝ := deriv x s

variable {z : ℝ → TranslatorState}
variable (hz : ∀ s, HasDerivAt z (translatorNumerator (z s)) s)
include hz

theorem theta_hasDerivAt (s : ℝ) : HasDerivAt (fun u => z u 0) (z s 1) s :=
  hasDerivAt_pi.mp (hz s) 0
theorem curvature_hasDerivAt (s : ℝ) : HasDerivAt (fun u => z u 1) (z s 2) s :=
  hasDerivAt_pi.mp (hz s) 1
theorem curvatureDerivative_hasDerivAt (s : ℝ) :
    HasDerivAt (fun u => z u 2) (-(z s 1)^3/2 + Real.sin (z s 0)) s :=
  hasDerivAt_pi.mp (hz s) 2

theorem betaX_hasDerivAt (s : ℝ) : HasDerivAt (betaX z) (Real.cos (z s 0)) s := by
  have hc := Real.continuous_cos.comp (contDiff_pi.mp (global_translator_smooth hz) 0).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
theorem betaY_hasDerivAt (s : ℝ) : HasDerivAt (betaY z) (Real.sin (z s 0)) s := by
  have hc := Real.continuous_sin.comp (contDiff_pi.mp (global_translator_smooth hz) 0).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem betaX_smooth : ContDiff ℝ ∞ (betaX z) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun s => (betaX_hasDerivAt hz s).differentiableAt, ?_⟩
  have he : deriv (betaX z) = fun s => Real.cos (z s 0) :=
    funext fun s => (betaX_hasDerivAt hz s).deriv
  rw [he]
  exact (contDiff_pi.mp (global_translator_smooth hz) 0).cos
theorem betaY_smooth : ContDiff ℝ ∞ (betaY z) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun s => (betaY_hasDerivAt hz s).differentiableAt, ?_⟩
  have he : deriv (betaY z) = fun s => Real.sin (z s 0) :=
    funext fun s => (betaY_hasDerivAt hz s).deriv
  rw [he]
  exact (contDiff_pi.mp (global_translator_smooth hz) 0).sin

theorem positionX_joint_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => positionX z p.1 p.2) :=
  ((betaX_smooth hz).comp contDiff_snd).add contDiff_fst
theorem positionY_joint_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => positionY z p.1 p.2) :=
  (betaY_smooth hz).comp contDiff_snd

theorem position_joint_smooth :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => (positionX z p.1 p.2, positionY z p.1 p.2)) :=
  (positionX_joint_smooth hz).prodMk (positionY_joint_smooth hz)

theorem positionX_spatial_derivative (t s : ℝ) :
    deriv (positionX z t) s = Real.cos (z s 0) :=
  ((betaX_hasDerivAt hz s).add_const t).deriv
theorem positionY_spatial_derivative (t s : ℝ) :
    deriv (positionY z t) s = Real.sin (z s 0) := (betaY_hasDerivAt hz s).deriv
theorem positionX_second_derivative (t s : ℝ) :
    deriv (deriv (positionX z t)) s = -Real.sin (z s 0) * z s 1 := by
  rw [show deriv (positionX z t) = fun u => Real.cos (z u 0) from
    funext (positionX_spatial_derivative hz t)]
  exact ((theta_hasDerivAt hz s).cos).deriv
theorem positionY_second_derivative (t s : ℝ) :
    deriv (deriv (positionY z t)) s = Real.cos (z s 0) * z s 1 := by
  rw [show deriv (positionY z t) = fun u => Real.sin (z u 0) from
    funext (positionY_spatial_derivative hz t)]
  exact ((theta_hasDerivAt hz s).sin).deriv

/-- The actual Euclidean squared speed is one at every time and parameter. -/
theorem unit_speed (t s : ℝ) : speedSquared (positionX z t) (positionY z t) s = 1 := by
  rw [speedSquared, positionX_spatial_derivative hz, positionY_spatial_derivative hz]
  nlinarith [Real.sin_sq_add_cos_sq (z s 0)]

theorem tangent_ne_zero (t s : ℝ) :
    (deriv (positionX z t) s, deriv (positionY z t) s) ≠ (0, 0) := by
  intro he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  have hu := unit_speed hz t s
  dsimp only [Prod.fst, Prod.snd] at hx hy
  simp [speedSquared, hx, hy] at hu

/-- This determinant is the signed curvature because actual unit speed was proved. -/
theorem signedCurvature_eq (t s : ℝ) :
    signedCurvature (positionX z t) (positionY z t) s = z s 1 := by
  rw [signedCurvature, positionX_spatial_derivative hz, positionY_spatial_derivative hz,
    positionX_second_derivative hz, positionY_second_derivative hz]
  calc
    _ = z s 1 * (Real.sin (z s 0)^2 + Real.cos (z s 0)^2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one]

/-- Elastic force computed from the actual reconstructed position curvature. -/
theorem elasticForce_eq (t s : ℝ) :
    elasticForce (positionX z t) (positionY z t) s = Real.sin (z s 0) := by
  have hc : signedCurvature (positionX z t) (positionY z t) = fun u => z u 1 :=
    funext (signedCurvature_eq hz t)
  have hv : deriv (fun u => z u 1) = fun u => z u 2 :=
    funext fun u => (curvature_hasDerivAt hz u).deriv
  rw [elasticForce, hc, hv, (curvatureDerivative_hasDerivAt hz s).deriv]
  ring

theorem normalX_eq (t s : ℝ) :
    normalX (positionX z t) (positionY z t) s = -Real.sin (z s 0) := by
  rw [normalX, positionY_spatial_derivative hz]
theorem normalY_eq (t s : ℝ) :
    normalY (positionX z t) (positionY z t) s = Real.cos (z s 0) := by
  rw [normalY, positionX_spatial_derivative hz]

theorem normal_unit (t s : ℝ) :
    normalX (positionX z t) (positionY z t) s ^ 2 +
      normalY (positionX z t) (positionY z t) s ^ 2 = 1 := by
  rw [normalX_eq hz, normalY_eq hz]
  simpa only [neg_sq] using Real.sin_sq_add_cos_sq (z s 0)

omit hz in
theorem normal_orthogonal (t s : ℝ) :
    deriv (positionX z t) s * normalX (positionX z t) (positionY z t) s +
      deriv (positionY z t) s * normalY (positionX z t) (positionY z t) s = 0 := by
  dsimp [normalX, normalY]
  ring

omit hz in
theorem positionX_time_derivative (t s : ℝ) :
    deriv (fun u => positionX z u s) t = 1 := ((hasDerivAt_id t).const_add (betaX z s)).deriv
omit hz in
theorem positionY_time_derivative (t s : ℝ) :
    deriv (fun u => positionY z u s) t = 0 := (hasDerivAt_const t (betaY z s)).deriv

omit hz in
def normalSpeed (z : ℝ → TranslatorState) (t s : ℝ) : ℝ :=
  deriv (fun u => positionX z u s) t * normalX (positionX z t) (positionY z t) s +
    deriv (fun u => positionY z u s) t * normalY (positionX z t) (positionY z t) s

/-- The normal component of the actual translating velocity is minus elastic force. -/
theorem normalSpeed_eq_neg_force (t s : ℝ) :
    normalSpeed z t s = -elasticForce (positionX z t) (positionY z t) s := by
  rw [normalSpeed, positionX_time_derivative, positionY_time_derivative,
    normalX_eq hz, elasticForce_eq hz]
  ring

theorem normal_projection_equation (t s : ℝ) :
    (normalSpeed z t s * normalX (positionX z t) (positionY z t) s,
      normalSpeed z t s * normalY (positionX z t) (positionY z t) s) =
    (-elasticForce (positionX z t) (positionY z t) s * normalX (positionX z t) (positionY z t) s,
      -elasticForce (positionX z t) (positionY z t) s * normalY (positionX z t) (positionY z t) s) := by
  rw [normalSpeed_eq_neg_force hz]

omit hz in
def pullbackMetric (z : ℝ → TranslatorState) (t s u w : ℝ) : ℝ :=
  (u * deriv (positionX z t) s) * (w * deriv (positionX z t) s) +
    (u * deriv (positionY z t) s) * (w * deriv (positionY z t) s)

theorem pullbackMetric_eq (t s u w : ℝ) : pullbackMetric z t s u w = u * w := by
  calc
    _ = u * w * speedSquared (positionX z t) (positionY z t) s := by
      dsimp [pullbackMetric, speedSquared]
      ring
    _ = _ := by rw [unit_speed hz, mul_one]

omit hz in
def intrinsicDistance (z : ℝ → TranslatorState) (t a b : ℝ) : ℝ :=
  |∫ s in a..b, Real.sqrt (speedSquared (positionX z t) (positionY z t) s)|

theorem intrinsicDistance_eq (t a b : ℝ) : intrinsicDistance z t a b = dist a b := by
  have hspeed : (fun s => Real.sqrt (speedSquared (positionX z t) (positionY z t) s)) =
      fun _ => (1:ℝ) := by funext s; rw [unit_speed hz, Real.sqrt_one]
  rw [intrinsicDistance, hspeed]
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, Real.dist_eq]
  exact abs_sub_comm b a

/-- The induced metric tensor and intrinsic distance are exactly the complete
standard real-line metric. This makes the completeness claim explicit. -/
theorem intrinsic_metric_complete :
    (∀ t s u w, pullbackMetric z t s u w = u*w) ∧
    (∀ t a b, intrinsicDistance z t a b = dist a b) ∧ CompleteSpace ℝ :=
  ⟨pullbackMetric_eq hz, intrinsicDistance_eq hz, inferInstance⟩

theorem initial_nonzero_curvature
    (h0 : z 0 = ![Real.pi/2, 1, 0]) (t : ℝ) :
    signedCurvature (positionX z t) (positionY z t) 0 = 1 := by
  rw [signedCurvature_eq hz, h0]
  rfl

theorem initial_nonzero_normal_motion
    (h0 : z 0 = ![Real.pi/2, 1, 0]) (t : ℝ) : normalSpeed z t 0 = -1 := by
  rw [normalSpeed_eq_neg_force hz, elasticForce_eq hz, h0]
  simp [Real.sin_pi_div_two]

/-- The example is not contained in any affine line with nonzero normal. -/
theorem not_in_affine_line
    (h0 : z 0 = ![Real.pi/2, 1, 0]) :
    ¬ ∃ A B C : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ s, A * betaX z s + B * betaY z s = C := by
  rintro ⟨A, B, C, hnonzero, hline⟩
  have hderiv (s : ℝ) : A * Real.cos (z s 0) + B * Real.sin (z s 0) = 0 := by
    have hd := ((betaX_hasDerivAt hz s).const_mul A).add ((betaY_hasDerivAt hz s).const_mul B)
    change HasDerivAt (fun u => A * betaX z u + B * betaY z u)
      (A * Real.cos (z s 0) + B * Real.sin (z s 0)) s at hd
    have he : (fun u => A * betaX z u + B * betaY z u) = fun _ => C := funext hline
    rw [he] at hd
    exact hd.unique (hasDerivAt_const s C)
  have hB : B = 0 := by simpa [h0, Real.sin_pi_div_two, Real.cos_pi_div_two] using hderiv 0
  have hd := (((theta_hasDerivAt hz 0).cos).const_mul A).add
    (((theta_hasDerivAt hz 0).sin).const_mul B)
  change HasDerivAt (fun u => A * Real.cos (z u 0) + B * Real.sin (z u 0))
    (A * (-Real.sin (z 0 0) * z 0 1) + B * (Real.cos (z 0 0) * z 0 1)) 0 at hd
  have he : (fun u => A * Real.cos (z u 0) + B * Real.sin (z u 0)) = fun _ => (0:ℝ) :=
    funext hderiv
  rw [he] at hd
  have hA : A = 0 := by
    have hh := hd.unique (hasDerivAt_const 0 (0:ℝ))
    simpa [h0, hB, Real.sin_pi_div_two, Real.cos_pi_div_two] using hh
  exact hnonzero.elim (fun h => h hA) (fun h => h hB)

omit hz in
/-- An actual global nonstraight translator with nonzero normal motion. The
geometric equation and completeness properties above apply to this witness. -/
theorem exists_nonstraight_translator : ∃ z : ℝ → TranslatorState,
    z 0 = ![Real.pi/2, 1, 0] ∧
    (∀ s, HasDerivAt z (translatorNumerator (z s)) s) ∧
    ContDiff ℝ ∞ z ∧
    (¬ ∃ A B C : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ s, A*betaX z s+B*betaY z s=C) ∧
    (∀ t, normalSpeed z t 0 = -1) := by
  obtain ⟨z, hz0, hz⟩ := exists_global_translator ![Real.pi/2, 1, 0]
  exact ⟨z, hz0, hz, global_translator_smooth hz,
    not_in_affine_line hz hz0, initial_nonzero_normal_motion hz hz0⟩

omit hz in
/-- A concrete global geometric translator, with intrinsic completeness
expressed by its actual metric tensor and distance, and nonzero normal motion. -/
theorem exists_complete_nonstraight_geometric_translator : ∃ z : ℝ → TranslatorState,
    z 0 = ![Real.pi/2, 1, 0] ∧
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => (positionX z p.1 p.2, positionY z p.1 p.2)) ∧
    (∀ t s, speedSquared (positionX z t) (positionY z t) s = 1) ∧
    (∀ t s, normalSpeed z t s = -elasticForce (positionX z t) (positionY z t) s) ∧
    (∀ t s u w, pullbackMetric z t s u w = u*w) ∧
    (∀ t a b, intrinsicDistance z t a b = dist a b) ∧
    CompleteSpace ℝ ∧
    (¬ ∃ A B C : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ s, A*betaX z s+B*betaY z s=C) ∧
    (∀ t, normalSpeed z t 0 = -1) := by
  obtain ⟨z, hz0, hz⟩ := exists_global_translator ![Real.pi/2, 1, 0]
  exact ⟨z, hz0, position_joint_smooth hz, unit_speed hz,
    normalSpeed_eq_neg_force hz, pullbackMetric_eq hz, intrinsicDistance_eq hz,
    inferInstance, not_in_affine_line hz hz0, initial_nonzero_normal_motion hz hz0⟩

end
end OpenTranslator.TranslatorGeometry

#print axioms OpenTranslator.TranslatorGeometry.exists_nonstraight_translator
#print axioms OpenTranslator.TranslatorGeometry.exists_complete_nonstraight_geometric_translator

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`OpenTranslator).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
      checked := checked + 1
  logInfo m!"Geometry: audited {checked} declarations; standard axioms only."
