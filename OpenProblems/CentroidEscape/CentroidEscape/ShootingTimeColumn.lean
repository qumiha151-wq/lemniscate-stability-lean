import CentroidEscape.ShootingProbeBridge
import CentroidEscape.FiniteDifferenceDerivative
import CentroidEscape.BallExpression

/-!
# The terminal-time Jacobian column from the center endpoint alone

The actual initial data are independent of L. Thus the L column equals the
projected original field at the terminal state. Existing rational-ball field
evaluation certifies it without either L+delta or L-delta integration.
-/
namespace CentroidEscape.MetricStability
noncomputable section
open Set Real
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

lemma shootingInitialLinear_timeDirection : shootingInitialLinear (coordinateDirection 2)=0 := by
  ext i
  fin_cases i <;> simp [shootingInitialLinear,coordinateDirection]

lemma shootingInputLinear_timeDirection : shootingInputLinear (coordinateDirection 2)=(1,0) := by
  simp only [shootingInputLinear,ContinuousLinearMap.prod_apply,ContinuousLinearMap.proj_apply,
    shootingInitialLinear_timeDirection]
  simp [coordinateDirection]

theorem actualShootingDifferential_time_column (U : ℝ) (hU : 0≤U) (p : Fin 3 → ℝ) :
    actualShootingDifferential U hU p (coordinateDirection 2)=
      shootingProjection (clippedField (shootingFlow U hU (p 2) (shootingInitial p))) := by
  simp only [actualShootingDifferential,ContinuousLinearMap.comp_apply,
    shootingInputLinear_timeDirection,shootingFlowDifferential,
    ContinuousLinearMap.coprod_apply,ContinuousLinearMap.toSpanSingleton_apply,
    map_zero,add_zero,one_smul,shootingProjectionLinear_eq]

theorem actualShooting_fderiv_time_column_extended {T : ℝ} (hT : 0<T)
    {p₀ : Fin 3 → ℝ} (hcenter : p₀ 2=T)
    (hc : ∀ t∈Icc 0 T, shootingFlow T hT.le t (shootingInitial p₀)∈innerWeightedTube) :
    (fderiv ℝ (actualShootingMap (shootingExtendedHorizon T)
      (shootingExtendedHorizon_nonneg hT.le)) p₀) (coordinateDirection 2)=
      shootingProjection (weightedField (shootingFlow (shootingExtendedHorizon T)
        (shootingExtendedHorizon_nonneg hT.le) (p₀ 2) (shootingInitial p₀))) := by
  have hp₀ : p₀∈Metric.ball p₀ (metricShootingParameterRadius T) :=
    Metric.mem_ball_self (metricShootingParameterRadius_pos hT)
  have hd := actualShootingMap_hasFDerivAt_metric_extended hT hcenter hc hp₀
  have htime := (metricShootingParameterRadius_domain hcenter hp₀).1
  have htube := shootingFlow_extended_metric_tube T hT.le hc (shootingInitial p₀)
    (Metric.mem_ball_self (metricShootingRadius_pos T)) (p₀ 2) (Ioo_subset_Icc_self htime)
  rw [hd.fderiv,actualShootingDifferential_time_column,clippedField_eq htube]

/-- Only rational operations and the existing proved field-ball evaluator
are required to certify the actual L derivative column. -/
theorem shooting_time_column_error {T : ℝ} (hT : 0<T)
    {p₀ : Fin 3 → ℝ} (hcenter : p₀ 2=T)
    (hc : ∀ t∈Icc 0 T, shootingFlow T hT.le t (shootingInitial p₀)∈innerWeightedTube)
    {S : ℕ} (hS : 0<S) {b : BallVector}
    (hb : ∀ i, (b i).Contains (shootingFlow (shootingExtendedHorizon T)
      (shootingExtendedHorizon_nonneg hT.le) (p₀ 2) (shootingInitial p₀) i))
    {η : ℚ} (hη : 0≤η)
    (hrad : ∀ i, (projectBallVector (evaluateWeightedField S b) i).radius≤η) :
    ‖projectedBallCenter (evaluateWeightedField S b)-
      (fderiv ℝ (actualShootingMap (shootingExtendedHorizon T)
        (shootingExtendedHorizon_nonneg hT.le)) p₀) (coordinateDirection 2)‖≤(η:ℝ) := by
  rw [actualShooting_fderiv_time_column_extended hT hcenter hc]
  exact projectedBallCenter_error hη (evaluateWeightedField_contains hS hb) hrad

/-- Sum the column errors, allowing an inexpensive accurate time column
and two finite-difference columns to have different error budgets. -/
theorem columnOperator_error_sum (col : Fin 3 → (Fin 3 → ℝ))
    (A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) (ε : Fin 3 → ℝ)
    (hε : ∀ i, 0≤ε i) (hcol : ∀ i, ‖col i-A (coordinateDirection i)‖≤ε i) :
    ‖columnOperator col-A‖≤∑ i : Fin 3, ε i := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun i _=>hε i))
  intro v
  have he : (columnOperator col-A) v=∑ i : Fin 3, v i • (col i-A (coordinateDirection i)) := by
    rw [sub_apply,columnOperator_apply]
    conv_lhs => rhs; rw [coordinate_decomposition v]
    simp only [map_sum,map_smul,Finset.sum_sub_distrib,smul_sub]
  rw [he]
  calc
    _ ≤ ∑ i : Fin 3, ‖v i • (col i-A (coordinateDirection i))‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖v‖*ε i := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm v i) (hcol i) (norm_nonneg _) (norm_nonneg v)
    _ = (∑ i : Fin 3, ε i)*‖v‖ := by rw [← Finset.mul_sum]; ring

end
end CentroidEscape.MetricStability

#print axioms CentroidEscape.MetricStability.shooting_time_column_error

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape.MetricStability).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked+1
  logInfo m!"Center-only time-column audit passed for {checked} declarations."
