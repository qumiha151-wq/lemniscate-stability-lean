import CentroidEscape.SpatialRegularity
import CentroidEscape.IntegralReparam

/-!
# Intrinsic free-elastic force of the actual reparametrized immersion

The geometric force is defined from the actual curve's speed and unit tangent,
then differentiated in arclength. No original-profile force is supplied as an
input. This module does not assert C-infinity spatial parameter dependence.
-/

namespace CentroidEscape
noncomputable section
set_option backward.isDefEq.respectTransparency false

def curveArcDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (γ : ℝ → Plane) (f : ℝ → E) (s : ℝ) : E :=
  ‖deriv γ s‖⁻¹ • deriv f s

def curveUnitTangent (γ : ℝ → Plane) (s : ℝ) : Plane := curveArcDerivative γ γ s

def rotatePlane (v : Plane) : Plane := planePair (-(v 1)) (v 0)

def curveUnitNormal (γ : ℝ → Plane) (s : ℝ) : Plane := rotatePlane (curveUnitTangent γ s)

def curveSignedCurvature (γ : ℝ → Plane) (s : ℝ) : ℝ :=
  inner ℝ (curveArcDerivative γ (curveUnitTangent γ) s) (curveUnitNormal γ s)

def curveElasticForce (γ : ℝ → Plane) (s : ℝ) : ℝ :=
  curveArcDerivative γ (curveArcDerivative γ (curveSignedCurvature γ)) s +
    curveSignedCurvature γ s ^ 3 / 2

def reparametrizedProfile (q : ℝ → State) (R : ℝ) (φ : ℝ → ℝ) (s : ℝ) : Plane :=
  R • position (q (φ s))

section Geometry
variable {q : ℝ → State} {φ J : ℝ → ℝ} {R : ℝ}
variable (hq : ∀ s, HasDerivAt q (field (q s)) s)
variable (hu : ∀ s, tangentSquare (q s) = 1)
variable (hφ : ∀ s, HasDerivAt φ (J s) s) (hJ : ∀ s, 0 < J s) (hR : 0 < R)

include hq hφ in
lemma reparametrizedProfile_hasDerivAt (s : ℝ) :
    HasDerivAt (reparametrizedProfile q R φ) (J s • (R • tangent (q (φ s)))) s := by
  have hh := ((position_derivative (hq (φ s))).scomp s (hφ s)).const_smul R
  convert! hh using 1
  rw [smul_smul, smul_smul]
  congr 1
  ring

include hq hu hφ hJ hR

lemma reparametrizedProfile_speed (s : ℝ) :
    ‖deriv (reparametrizedProfile q R φ) s‖ = J s * R := by
  rw [(reparametrizedProfile_hasDerivAt hq hφ s).deriv,
    norm_smul, norm_smul, tangent_norm_one (hu _), Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (hJ s), abs_of_pos hR, mul_one]

lemma reparametrizedProfile_arc_chain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {f' : E} {s : ℝ} (hf : HasDerivAt f f' (φ s)) :
    curveArcDerivative (reparametrizedProfile q R φ) (fun r => f (φ r)) s = R⁻¹ • f' := by
  have hd : HasDerivAt (fun r => f (φ r)) (J s • f') s := by
    convert! hf.scomp s (hφ s) using 1
  rw [curveArcDerivative, reparametrizedProfile_speed hq hu hφ hJ hR, hd.deriv, smul_smul]
  congr 1
  field_simp [(hJ s).ne', hR.ne']

theorem reparametrizedProfile_unit_tangent (s : ℝ) :
    curveUnitTangent (reparametrizedProfile q R φ) s = tangent (q (φ s)) := by
  rw [curveUnitTangent, curveArcDerivative,
    reparametrizedProfile_speed hq hu hφ hJ hR,
    (reparametrizedProfile_hasDerivAt hq hφ s).deriv, smul_smul, smul_smul]
  have hc : (J s * R)⁻¹ * (J s * R) = 1 := inv_mul_cancel₀ (mul_ne_zero (hJ s).ne' hR.ne')
  rw [mul_assoc, hc, one_smul]

theorem reparametrizedProfile_unit_normal (s : ℝ) :
    curveUnitNormal (reparametrizedProfile q R φ) s = normal (q (φ s)) := by
  rw [curveUnitNormal, reparametrizedProfile_unit_tangent hq hu hφ hJ hR]
  simp [rotatePlane, tangent, normal, planePair]

theorem reparametrizedProfile_curvature (s : ℝ) :
    curveSignedCurvature (reparametrizedProfile q R φ) s = q (φ s) 4 / R := by
  have hT : curveUnitTangent (reparametrizedProfile q R φ) = fun r => tangent (q (φ r)) :=
    funext (reparametrizedProfile_unit_tangent hq hu hφ hJ hR)
  rw [curveSignedCurvature, hT, reparametrizedProfile_unit_normal hq hu hφ hJ hR,
    reparametrizedProfile_arc_chain hq hu hφ hJ hR (tangent_derivative (hq (φ s))),
    smul_smul, real_inner_smul_left, real_inner_self_eq_norm_sq, normal_norm_one (hu _)]
  simp [div_eq_mul_inv, mul_comm]

theorem reparametrizedProfile_curvature_first (s : ℝ) :
    curveArcDerivative (reparametrizedProfile q R φ)
      (curveSignedCurvature (reparametrizedProfile q R φ)) s = q (φ s) 5 / R^2 := by
  have hk : curveSignedCurvature (reparametrizedProfile q R φ) = fun r => q (φ r) 4 / R :=
    funext (reparametrizedProfile_curvature hq hu hφ hJ hR)
  rw [hk]
  have hd := (curvature_derivative (hq (φ s))).div_const R
  rw [reparametrizedProfile_arc_chain hq hu hφ hJ hR hd]
  simp only [smul_eq_mul]
  ring

theorem reparametrizedProfile_curvature_second (s : ℝ) :
    curveArcDerivative (reparametrizedProfile q R φ)
      (curveArcDerivative (reparametrizedProfile q R φ)
        (curveSignedCurvature (reparametrizedProfile q R φ))) s =
      (-(q (φ s) 4)^3/2 + q (φ s) 0*q (φ s) 3 - q (φ s) 1*q (φ s) 2) / R^3 := by
  have hk : curveArcDerivative (reparametrizedProfile q R φ)
      (curveSignedCurvature (reparametrizedProfile q R φ)) = fun r => q (φ r) 5 / R^2 :=
    funext (reparametrizedProfile_curvature_first hq hu hφ hJ hR)
  rw [hk]
  have hd := (hasDerivAt_pi.mp (hq (φ s)) 5).div_const (R^2)
  rw [reparametrizedProfile_arc_chain hq hu hφ hJ hR hd]
  simp only [smul_eq_mul]
  dsimp [field]
  ring

/-- Force built from the actual curve and arclength differentiation agrees
with the force computed in the original unit-speed coordinate. -/
theorem reparametrizedProfile_force (s : ℝ) :
    curveElasticForce (reparametrizedProfile q R φ) s = scaledForce q R (R * φ s) := by
  rw [curveElasticForce, reparametrizedProfile_curvature_second hq hu hφ hJ hR,
    reparametrizedProfile_curvature hq hu hφ hJ hR, scaledForce_eq hq]
  rw [mul_div_cancel_left₀ _ hR.ne', position_normal_inner]
  ring

end Geometry

theorem coherentExpandingCurve_spatial_C1 {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hp : Function.Periodic q P) (hP : P ≠ 0) (t : ℝ) :
    ContDiff ℝ 1 (coherentExpandingCurve hq hp hP t) := by
  have hpos : ContDiff ℝ 1 (fun s => position (q s)) := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun s => (position_derivative (hq s)).differentiableAt, ?_⟩
    have hd : deriv (fun s => position (q s)) = fun s => tangent (q s) :=
      funext fun s => (position_derivative (hq s)).deriv
    rw [hd]
    have hc : Continuous q := continuous_iff_continuousAt.mpr fun s => (hq s).continuousAt
    unfold tangent planePair
    fun_prop
  exact (hpos.comp (profileParameterLift_C1 hq hp hP t)).const_smul (expanderRadius t)

theorem coherentExpandingCurve_periodic {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hp : Function.Periodic q P) (hP : P ≠ 0) (t : ℝ) :
    Function.Periodic (coherentExpandingCurve hq hp hP t) P := by
  intro s
  unfold coherentExpandingCurve profileParameterLift
  rw [parameterFlow_period_lift _ (profileParameterData_periodic hq hp hP),
    expandingCurve_periodic hp t]

theorem coherentExpandingCurve_initial {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hp : Function.Periodic q P) (hP : P ≠ 0) (s : ℝ) :
    coherentExpandingCurve hq hp hP 0 s = position (q s) := by
  simp [coherentExpandingCurve, profileParameterLift, logarithmicTime_zero,
    parameterFlow_zero, expandingCurve, expanderRadius]

theorem coherentExpandingCurve_geometric_FEF {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hu : ∀ s, tangentSquare (q s) = 1)
    (hp : Function.Periodic q P) (hP : P ≠ 0) {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    HasDerivAt (fun r => coherentExpandingCurve hq hp hP r s)
      ((-curveElasticForce (coherentExpandingCurve hq hp hP t) s) •
        curveUnitNormal (coherentExpandingCurve hq hp hP t) s) t := by
  have hφ := profileParameterLift_initial_derivative hq hp hP t
  have hJ := parameterJacobian_pos (profileParameterData hq hp hP) (logarithmicTime t)
  have hF := reparametrizedProfile_force hq hu hφ hJ (expanderRadius_pos ht) s
  have hN := reparametrizedProfile_unit_normal hq hu hφ hJ (expanderRadius_pos ht) s
  change curveElasticForce (coherentExpandingCurve hq hp hP t) s =
      scaledForce q (expanderRadius t) (expanderRadius t * profileParameterLift hq hp hP t s) at hF
  change curveUnitNormal (coherentExpandingCurve hq hp hP t) s =
      normal (q (profileParameterLift hq hp hP t s)) at hN
  rw [hF, hN]
  exact coherent_reparametrized_vector_FEF hq hu hp hP ht s

/-- All geometric/parameter and centroid conclusions from exact shooting data.
The remaining numerical task is to construct these exact input data. The
regularity asserted here is spatial C1 plus the actual intrinsic force PDE;
C-infinity dependence is not claimed. -/
theorem exact_half_orbit_yields_intrinsic_FEF_escape {z : ℝ → State} {m : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L)
    (hz : ∀ s ∈ Set.Icc (0:ℝ) L, HasDerivAt z (field (z s)) s)
    (h0 : reverseState (z 0) = z 0) (hfix : reverseState (z L) = z L)
    (hu : z 0 2 = 0) (hw : z 0 3 = 1)
    (hm : ∀ s ∈ Set.Icc (0:ℝ) L, HasDerivAt m (z s 0) s)
    (hm0 : m 0 = 0) (hmpos : 0 < m L) :
    ∃ γ : ℝ → ℝ → Plane,
      (∀ t, Function.Periodic (γ t) (2*L) ∧ ContDiff ℝ 1 (γ t)) ∧
      (∀ t, 0 ≤ t → ∀ s, 0 < ‖deriv (γ t) s‖) ∧
      (∀ t, 0 ≤ t → ∀ s, HasDerivAt (fun r => γ r s)
        ((-curveElasticForce (γ t) s) • curveUnitNormal (γ t) s) t) ∧
      Filter.Tendsto (fun t => curveCentroidX (2*L) (γ t)) Filter.atTop Filter.atTop := by
  obtain ⟨q, hp, _, hq, hunit, _, _, hesc⟩ :=
    exact_half_orbit_yields_centroid_escape hL hz h0 hfix hu hw hm hm0 hmpos
  have hP : 2*L ≠ 0 := by positivity
  refine ⟨coherentExpandingCurve hq hp hP, ?_, ?_, ?_, ?_⟩
  · intro t
    exact ⟨coherentExpandingCurve_periodic hq hp hP t,
      coherentExpandingCurve_spatial_C1 hq hp hP t⟩
  · intro t ht s
    exact reparametrized_spatial_speed_pos hq hunit hp hP ht s
  · intro t ht s
    exact coherentExpandingCurve_geometric_FEF hq hunit hp hP ht s
  · apply hesc.congr'
    filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with t ht
    exact (coherentExpandingCurve_centroid hq hunit hp hP ht).symm

end
end CentroidEscape

#print axioms CentroidEscape.reparametrizedProfile_force
#print axioms CentroidEscape.coherentExpandingCurve_geometric_FEF

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Centroid intrinsic-force audit passed for {checked} declarations."
