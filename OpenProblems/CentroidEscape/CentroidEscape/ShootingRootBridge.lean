import CentroidEscape.FiniteDifferenceDerivative

/-!
# From seven endpoint enclosures to an exact actual shooting zero

The certificate inputs are finite endpoint errors, a finite approximate
Jacobian/preconditioner check, and a checked interior reference trajectory.
Actual differentiability and uniform derivative estimates are conclusions
of the preceding ODE arguments, not certificate assumptions here.
-/
namespace CentroidEscape
noncomputable section
open Set Real
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem exists_actual_shooting_root_of_endpoint_certificate
    {T : ℝ} (hT : 0<T) (hTmin : 1≤T) (hbudget : shootingExtendedHorizon T≤15/2)
    {p₀ : Fin 3 → ℝ} (hcenter : p₀ 2=T)
    (hc : ∀t∈Icc 0 T, shootingFlow T hT.le t (shootingInitial p₀)∈innerWeightedTube)
    {δ η r β q₀ ζ : ℝ} (q : ℝ≥0)
    (hη : 0≤η) (hδ : 0<δ) (hδR : δ<1/10^13)
    (hr : 0≤r) (hrR : r<1/10^13) (hβ : 0≤β) (hq : q<1)
    (yp ym : Fin 3 → (Fin 3 → ℝ)) (y₀ : Fin 3 → ℝ)
    (B : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))
    (hp : ∀ i, ‖yp i-actualShootingMap (shootingExtendedHorizon T)
      (shootingExtendedHorizon_nonneg hT.le) (p₀+δ • coordinateDirection i)‖≤η)
    (hm : ∀ i, ‖ym i-actualShootingMap (shootingExtendedHorizon T)
      (shootingExtendedHorizon_nonneg hT.le) (p₀-δ • coordinateDirection i)‖≤η)
    (hzero : ‖y₀-actualShootingMap (shootingExtendedHorizon T)
      (shootingExtendedHorizon_nonneg hT.le) p₀‖≤η)
    (hBnorm : ‖B‖≤β) (hBinj : Function.Injective B)
    (hmatrix : ‖ContinuousLinearMap.id ℝ (Fin 3 → ℝ)-
      B.comp (columnOperator (fun i=>(1/(2*δ):ℝ) • (yp i-ym i)))‖≤q₀)
    (hcenterResidual : ‖B y₀‖≤ζ)
    (hcontraction : q₀+β*(3*((6*10^14)*δ+η/δ)+(6*10^14)*r)≤(q:ℝ))
    (hself : (ζ+β*η)+(q:ℝ)*r≤r) :
    ∃ p∈Metric.closedBall p₀ r,
      actualShootingMap (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT.le) p=0 ∧
      ∀ p'∈Metric.closedBall p₀ r,
        actualShootingMap (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT.le) p'=0 → p'=p := by
  let U := shootingExtendedHorizon T
  let hU : 0≤U := shootingExtendedHorizon_nonneg hT.le
  let f := actualShootingMap U hU
  let D := fderiv ℝ f
  let J := columnOperator (fun i=>(1/(2*δ):ℝ) • (yp i-ym i))
  have hR := MetricStability.metricShootingParameterRadius_lower_bound hTmin hbudget
  have hsub : Metric.closedBall p₀ r ⊆
      Metric.ball p₀ (MetricStability.metricShootingParameterRadius T) := by
    intro p hp
    exact lt_of_le_of_lt hp (hrR.trans hR)
  have hcenterBall : p₀∈Metric.ball p₀ (MetricStability.metricShootingParameterRadius T) :=
    Metric.mem_ball_self (MetricStability.metricShootingParameterRadius_pos hT)
  have hF : ∀p∈Metric.closedBall p₀ r, HasFDerivAt f (D p) p := by
    intro p hp
    exact (MetricStability.actualShootingMap_hasFDerivAt_metric_extended hT hcenter hc
      (hsub hp)).differentiableAt.hasFDerivAt
  have hJ : ‖J-D p₀‖≤3*((6*10^14)*δ+η/δ) :=
    actualShooting_centralDifference_columns_error hT hTmin hbudget hcenter hc hη hδ hδR yp ym hp hm
  have hD : ∀p∈Metric.closedBall p₀ r,
      ‖ContinuousLinearMap.id ℝ (Fin 3 → ℝ)-B.comp (D p)‖≤(q:ℝ) := by
    intro p hpoint
    have hv : ‖D p-D p₀‖≤(6*10^14)*dist p p₀ :=
      MetricStability.actualShootingMap_fderiv_metric_extended_budget hT hbudget hcenter hc
        (hsub hpoint) hcenterBall
    exact (preconditioned_derivative_from_center D B J hβ (by positivity) hBnorm hJ hv
      hpoint hmatrix).trans hcontraction
  have hres : ‖B (f p₀)‖≤ζ+β*η := by
    have he : B (f p₀)=B y₀+B (f p₀-y₀) := by rw [map_sub]; abel
    have hn := norm_add_le (B y₀) (B (f p₀-y₀))
    have hb := B.le_opNorm (f p₀-y₀)
    have herror : ‖f p₀-y₀‖≤η := by simpa only [norm_sub_rev] using hzero
    have hm := mul_le_mul hBnorm herror (norm_nonneg _) hβ
    rw [he]
    linarith
  exact exists_unique_zero_of_preconditioned_bounds f D B p₀ r (ζ+β*η) q hr hq hBinj
    hF hD hres hself

end
end CentroidEscape

#print axioms CentroidEscape.exists_actual_shooting_root_of_endpoint_certificate

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked+1
  logInfo m!"Actual shooting-root bridge audit passed for {checked} declarations."
