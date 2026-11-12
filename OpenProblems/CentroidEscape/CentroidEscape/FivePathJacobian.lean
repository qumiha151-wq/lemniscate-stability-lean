import CentroidEscape.ShootingTimeColumn

/-!
# An actual shooting Jacobian certificate from five paths

Only the center and four spatial probes are needed. The time column is
evaluated from the center endpoint's proved field-ball enclosure.
-/
namespace CentroidEscape.MetricStability
noncomputable section
open Set Real
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

def spatialParameterIndex (i : Fin 2) : Fin 3 := ⟨i.val,Nat.lt_trans i.isLt (by decide)⟩

def fivePathJacobian (δ : ℝ) (yp ym : Fin 2 → (Fin 3 → ℝ)) (vt : Fin 3 → ℝ) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  columnOperator ![(1/(2*δ):ℝ) • (yp 0-ym 0),(1/(2*δ):ℝ) • (yp 1-ym 1),vt]

theorem fivePathJacobian_error {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)}
    {D : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)}
    {p : Fin 3 → ℝ} {R H δ η ηt : ℝ}
    (hH : 0≤H) (hη : 0≤η) (hηt : 0≤ηt) (hδ : 0<δ) (hδR : δ<R)
    (hderiv : ∀ x∈Metric.ball p R, HasFDerivAt f (D x) x)
    (hvariation : ∀ x∈Metric.ball p R, ‖D x-D p‖≤H*dist x p)
    (yp ym : Fin 2 → (Fin 3 → ℝ)) (vt : Fin 3 → ℝ)
    (hp : ∀ i, ‖yp i-f (p+δ • coordinateDirection (spatialParameterIndex i))‖≤η)
    (hm : ∀ i, ‖ym i-f (p-δ • coordinateDirection (spatialParameterIndex i))‖≤η)
    (ht : ‖vt-D p (coordinateDirection 2)‖≤ηt) :
    ‖fivePathJacobian δ yp ym vt-D p‖≤2*(H*δ+η/δ)+ηt := by
  have hspace (i : Fin 2) :
      ‖(1/(2*δ):ℝ) • (yp i-ym i)-D p (coordinateDirection (spatialParameterIndex i))‖≤H*δ+η/δ := by
    have h1 := centralDifference_endpoint_error hδ (hp i) (hm i)
    have h2 := centralDifference_error hH hδ hδR
      (coordinateDirection_norm (spatialParameterIndex i)) hderiv hvariation
    have htri := norm_sub_le_norm_sub_add_norm_sub ((1/(2*δ):ℝ) • (yp i-ym i))
      (centralDifference f p (coordinateDirection (spatialParameterIndex i)) δ)
      (D p (coordinateDirection (spatialParameterIndex i)))
    linarith
  let eps : Fin 3 → ℝ := ![H*δ+η/δ,H*δ+η/δ,ηt]
  have heps : ∀ i, 0≤eps i := by
    intro i
    fin_cases i <;> dsimp [eps]
    all_goals positivity
  have hcols : ∀ i,
      ‖![(1/(2*δ):ℝ) • (yp 0-ym 0),(1/(2*δ):ℝ) • (yp 1-ym 1),vt] i-
        D p (coordinateDirection i)‖≤eps i := by
    intro i
    fin_cases i
    · exact hspace 0
    · exact hspace 1
    · exact ht
  have he := columnOperator_error_sum _ (D p) eps heps hcols
  change ‖fivePathJacobian δ yp ym vt-D p‖≤_ at he
  refine he.trans_eq ?_
  simp [eps,Fin.sum_univ_succ]
  ring

/-- All derivative and time-column hypotheses are proved for the actual
shooting map. The remaining endpoint hypotheses are finite probe enclosures. -/
theorem actual_fivePathJacobian_error {T : ℝ} (hT : 0<T) (hTmin : 1≤T)
    (hbudget : shootingExtendedHorizon T≤15/2)
    {p₀ : Fin 3 → ℝ} (hcenter : p₀ 2=T)
    (hc : ∀ t∈Icc 0 T, shootingFlow T hT.le t (shootingInitial p₀)∈innerWeightedTube)
    {δ η : ℝ} (hη : 0≤η) (hδ : 0<δ) (hδR : δ<1/10^13)
    (yp ym : Fin 2 → (Fin 3 → ℝ))
    (hp : ∀ i, ‖yp i-actualShootingMap (shootingExtendedHorizon T)
      (shootingExtendedHorizon_nonneg hT.le) (p₀+δ • coordinateDirection (spatialParameterIndex i))‖≤η)
    (hm : ∀ i, ‖ym i-actualShootingMap (shootingExtendedHorizon T)
      (shootingExtendedHorizon_nonneg hT.le) (p₀-δ • coordinateDirection (spatialParameterIndex i))‖≤η)
    {S : ℕ} (hS : 0<S) {b : BallVector}
    (hb : ∀ i, (b i).Contains (shootingFlow (shootingExtendedHorizon T)
      (shootingExtendedHorizon_nonneg hT.le) (p₀ 2) (shootingInitial p₀) i))
    {ηt : ℚ} (hηt : 0≤ηt)
    (hrad : ∀ i, (projectBallVector (evaluateWeightedField S b) i).radius≤ηt) :
    ‖fivePathJacobian δ yp ym (projectedBallCenter (evaluateWeightedField S b))-
      fderiv ℝ (actualShootingMap (shootingExtendedHorizon T)
        (shootingExtendedHorizon_nonneg hT.le)) p₀‖≤2*((6*10^14)*δ+η/δ)+(ηt:ℝ) := by
  have hR := metricShootingParameterRadius_lower_bound hTmin hbudget
  have hsub : Metric.ball p₀ (1/10^13:ℝ) ⊆ Metric.ball p₀ (metricShootingParameterRadius T) :=
    Metric.ball_subset_ball hR.le
  apply fivePathJacobian_error (R:=1/10^13) (H:=6*10^14) (by positivity) hη
    (Rat.cast_nonneg.mpr hηt) hδ hδR (yp:=yp) (ym:=ym) (hp:=hp) (hm:=hm)
  · intro x hx
    exact (actualShootingMap_hasFDerivAt_metric_extended hT hcenter hc
      (hsub hx)).differentiableAt.hasFDerivAt
  · intro x hx
    exact actualShootingMap_fderiv_metric_extended_budget hT hbudget hcenter hc
      (hsub hx) (Metric.mem_ball_self (metricShootingParameterRadius_pos hT))
  · exact shooting_time_column_error hT hcenter hc hS hb hηt hrad

theorem fivePath_newton_arithmetic_budget :
    (1/(10:ℝ)^9)+2*(2*((6*10^14)*(1/10^25)+(1/10^40)/(1/10^25))+
      (1/10^40)+(6*10^14)*(1/10^28))<2/10^9 := by norm_num

end
end CentroidEscape.MetricStability

#print axioms CentroidEscape.MetricStability.actual_fivePathJacobian_error

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
  logInfo m!"Five-path actual Jacobian audit passed for {checked} declarations."
