import CentroidEscape.Preconditioner

namespace CentroidEscape
noncomputable section
open Set Real
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- Generic actual shooting certificate bridge. The center Jacobian may
combine finite-difference initial columns with the exact endpoint-field time
column. The matrix defect itself certifies preconditioner injectivity. -/
theorem exists_actual_shooting_root_of_matrix_certificate
    {T : ℝ} (hT : 0<T) (hTmin : 1≤T) (hbudget : shootingExtendedHorizon T≤15/2)
    {p₀ : Fin 3 → ℝ} (hcenter : p₀ 2=T)
    (hc : ∀t∈Icc 0 T, shootingFlow T hT.le t (shootingInitial p₀)∈innerWeightedTube)
    {η ε r β q₀ ζ : ℝ} (q : ℝ≥0)
    (hr : 0≤r) (hrR : r<1/10^13) (hβ : 0≤β) (hq : q<1) (hq₀ : q₀<1)
    (y₀ : Fin 3 → ℝ) (B J : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))
    (hzero : ‖y₀-actualShootingMap (shootingExtendedHorizon T)
      (shootingExtendedHorizon_nonneg hT.le) p₀‖≤η)
    (hJ : ‖J-fderiv ℝ (actualShootingMap (shootingExtendedHorizon T)
      (shootingExtendedHorizon_nonneg hT.le)) p₀‖≤ε)
    (hBnorm : ‖B‖≤β)
    (hmatrix : ‖ContinuousLinearMap.id ℝ (Fin 3 → ℝ)-B.comp J‖≤q₀)
    (hcenterResidual : ‖B y₀‖≤ζ)
    (hcontraction : q₀+β*(ε+(6*10^14)*r)≤(q:ℝ))
    (hself : (ζ+β*η)+(q:ℝ)*r≤r) :
    ∃ p∈Metric.closedBall p₀ r,
      actualShootingMap (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT.le) p=0 ∧
      ∀ p'∈Metric.closedBall p₀ r,
        actualShootingMap (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT.le) p'=0 → p'=p := by
  let U := shootingExtendedHorizon T
  let hU : 0≤U := shootingExtendedHorizon_nonneg hT.le
  let f := actualShootingMap U hU
  let D := fderiv ℝ f
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
  exact exists_unique_zero_of_preconditioned_bounds f D B p₀ r (ζ+β*η) q hr hq
    (preconditioner_injective_of_defect B J (hmatrix.trans_lt hq₀)) hF hD hres hself

end
end CentroidEscape

#print axioms CentroidEscape.exists_actual_shooting_root_of_matrix_certificate

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
  logInfo m!"Actual shooting matrix-root bridge audit passed for {checked} declarations."
