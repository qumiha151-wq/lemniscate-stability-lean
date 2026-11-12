import CentroidEscape.MetricBootstrap

/-!
# Actual shooting initial data and projection in the diagonal metric

The input is the actual three-parameter (a,b,L) map. Final time does not
enter the initial state. The output is the actual unweighted (y,u,v).
-/
namespace CentroidEscape.MetricStability
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem shootingInitial_metricEnergy (p q : Fin 3 → ℝ) :
    metricEnergy (shootingInitial p-shootingInitial q)=
      (p 0-q 0)^2+(25/16)*(p 1-q 1)^2 := by
  simp [shootingInitial,metricEnergy]
  ring

theorem shootingInitial_metricEnergy_bound (p q : Fin 3 → ℝ) :
    metricEnergy (shootingInitial p-shootingInitial q)≤(41/16)*‖p-q‖^2 := by
  have hc (i : Fin 3) : (p i-q i)^2≤‖p-q‖^2 := by
    have hb : |p i-q i|≤‖p-q‖ := by
      simpa only [Real.norm_eq_abs,Pi.sub_apply] using norm_le_pi_norm (p-q) i
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (p i-q i)) (norm_nonneg (p-q))).mpr hb
  rw [shootingInitial_metricEnergy]
  nlinarith [hc 0,hc 1]

theorem shootingInitial_metric_bound (p q : Fin 3 → ℝ) :
    metricNorm (shootingInitial p-shootingInitial q)≤(13/8)*‖p-q‖ := by
  rw [metricNorm,Real.sqrt_le_left (by positivity : (0:ℝ)≤(13/8)*‖p-q‖)]
  nlinarith [shootingInitial_metricEnergy_bound p q,sq_nonneg ‖p-q‖]

theorem metricCoordinates_sq_le_energy (h : WeightedState) (i : Fin 7) :
    (metricCoordinates h i)^2≤metricEnergy h := by
  fin_cases i <;> simp only [metricCoordinates,Matrix.cons_val_zero',Matrix.cons_val_succ']
  all_goals dsimp [metricEnergy]
  all_goals nlinarith [sq_nonneg (h 0),sq_nonneg (h 1),sq_nonneg (h 2),
    sq_nonneg (h 3),sq_nonneg (h 4),sq_nonneg (h 5),sq_nonneg (h 6)]

theorem shootingProjection_metric_bound (h : WeightedState) :
    ‖shootingProjection h‖≤(5/2)*metricNorm h := by
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤5/2) (metricNorm_nonneg h))]
  intro i
  have he := metricNorm_sq h
  have hE := metricEnergy_nonneg h
  have hn := metricNorm_nonneg h
  have h1 := metricCoordinates_sq_le_energy h 1
  have h2 := metricCoordinates_sq_le_energy h 2
  have h5 := metricCoordinates_sq_le_energy h 5
  change (h 1)^2≤metricEnergy h at h1
  change (4*h 2)^2≤metricEnergy h at h2
  change ((128/5)*h 5)^2≤metricEnergy h at h5
  rw [Real.norm_eq_abs,abs_le]
  fin_cases i <;> simp only [shootingProjection,Matrix.cons_val_zero',Matrix.cons_val_succ']
  all_goals constructor <;> nlinarith

theorem shootingProjection_metric_difference (a b : WeightedState) :
    ‖shootingProjection a-shootingProjection b‖≤(5/2)*metricNorm (a-b) := by
  have he : shootingProjection a-shootingProjection b=shootingProjection (a-b) := by
    ext i
    fin_cases i <;> simp [shootingProjection] <;> ring
  rw [he]
  exact shootingProjection_metric_bound (a-b)

end
end CentroidEscape.MetricStability

#print axioms CentroidEscape.MetricStability.shootingInitial_metric_bound
#print axioms CentroidEscape.MetricStability.shootingProjection_metric_difference

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape.MetricStability).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Metric shooting-map audit passed for {checked} declarations."
