import CentroidEscape.MetricStability
import CentroidEscape.WeightedDerivatives

/-!
# Actual second derivative and midpoint defect in the diagonal metric

All estimates below concern the original polynomial vector field on its
convex tube. The metric is exactly MetricStability.metricNorm; no global
smoothness or small logarithmic norm is asserted for the clipped field.
-/
namespace CentroidEscape.MetricStability
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def plainEnergy (u : WeightedState) : ℝ :=
  (u 0)^2+(u 1)^2+(u 2)^2+(u 3)^2+(u 4)^2+(u 5)^2+(u 6)^2

def metricSecondCoordinates (c : ℝ) (u v : WeightedState) : WeightedState :=
  ![0,0,-(4/5)*(u 4*v 3+u 3*v 4),(4/5)*(u 4*v 2+u 2*v 4),0,
    -c*u 4*v 4+(2/5)*(u 0*v 3+u 3*v 0-u 1*v 2-u 2*v 1),0]

lemma plainEnergy_nonneg (u : WeightedState) : 0≤plainEnergy u := by
  dsimp [plainEnergy]; positivity

lemma plainEnergy_metricCoordinates (u : WeightedState) :
    plainEnergy (metricCoordinates u)=metricEnergy u := by
  simp [plainEnergy,metricCoordinates,metricEnergy]
  ring

lemma metricSecond_coordinate_identity (a u v : WeightedState) :
    metricCoordinates (weightedSecond a u v)=
      metricSecondCoordinates ((1536/125)*a 4) (metricCoordinates u) (metricCoordinates v) := by
  ext i
  fin_cases i <;> simp [metricCoordinates,metricSecondCoordinates,weightedSecond,
    weightedBilinear] <;> ring

lemma metricSecond_fifth_sq_le (c : ℝ) (u v : WeightedState)
    (hc : c^2≤(336/125:ℝ)^2) :
    (metricSecondCoordinates c u v 5)^2≤
      ((336/125:ℝ)^2*(u 4)^2+(4/25)*((u 0)^2+(u 1)^2+(u 2)^2+(u 3)^2))*
        plainEnergy v := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (![ (2/5)*u 3, -(2/5)*u 2, -(2/5)*u 1, (2/5)*u 0, -c*u 4] : Fin 5 → ℝ)
    (![v 0,v 1,v 2,v 3,v 4] : Fin 5 → ℝ)
  have hcs' : (metricSecondCoordinates c u v 5)^2≤
      (c^2*(u 4)^2+(4/25)*((u 0)^2+(u 1)^2+(u 2)^2+(u 3)^2))*
        ((v 0)^2+(v 1)^2+(v 2)^2+(v 3)^2+(v 4)^2) := by
    convert! hcs using 1 <;> (try simp [Fin.sum_univ_succ,metricSecondCoordinates]) <;> ring
  apply hcs'.trans
  apply mul_le_mul
  · nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg (u 4))]
  · dsimp [plainEnergy]; nlinarith [sq_nonneg (v 5),sq_nonneg (v 6)]
  · positivity
  · positivity

lemma metricSecond_plainEnergy_le (c : ℝ) (u v : WeightedState)
    (hc : c^2≤(336/125:ℝ)^2) :
    plainEnergy (metricSecondCoordinates c u v)≤9*plainEnergy u*plainEnergy v := by
  have h2 : (metricSecondCoordinates c u v 2)^2≤
      (32/25)*((u 4)^2*(v 3)^2+(u 3)^2*(v 4)^2) := by
    change (-(4/5)*(u 4*v 3+u 3*v 4))^2≤_
    nlinarith [sq_nonneg (u 4*v 3-u 3*v 4)]
  have h3 : (metricSecondCoordinates c u v 3)^2≤
      (32/25)*((u 4)^2*(v 2)^2+(u 2)^2*(v 4)^2) := by
    change ((4/5)*(u 4*v 2+u 2*v 4))^2≤_
    nlinarith [sq_nonneg (u 4*v 2-u 2*v 4)]
  have h5 := metricSecond_fifth_sq_le c u v hc
  have hb : 0≤9*plainEnergy u*plainEnergy v-
      ((32/25)*((u 4)^2*(v 3)^2+(u 3)^2*(v 4)^2)+
       (32/25)*((u 4)^2*(v 2)^2+(u 2)^2*(v 4)^2)+
       ((336/125:ℝ)^2*(u 4)^2+(4/25)*((u 0)^2+(u 1)^2+(u 2)^2+(u 3)^2))*
         plainEnergy v) := by
    dsimp [plainEnergy]
    ring_nf
    positivity
  have he : plainEnergy (metricSecondCoordinates c u v)=
      (metricSecondCoordinates c u v 2)^2+(metricSecondCoordinates c u v 3)^2+
      (metricSecondCoordinates c u v 5)^2 := by
    simp [plainEnergy,metricSecondCoordinates]
  linarith

/-- A genuine Hessian estimate, with respect to the already defined metric. -/
theorem weightedSecond_metric_bound {a : WeightedState} (ha : a∈weightedTube)
    (u v : WeightedState) : metricNorm (weightedSecond a u v)≤3*metricNorm u*metricNorm v := by
  have ha4 := (tube_coordinates ha).2.2.2.2.1
  have hc : (((1536/125:ℝ)*a 4))^2≤(336/125:ℝ)^2 := by
    rcases abs_le.mp ha4 with ⟨hl,hr⟩
    nlinarith [sq_nonneg (a 4)]
  have hb := metricSecond_plainEnergy_le ((1536/125)*a 4)
    (metricCoordinates u) (metricCoordinates v) hc
  rw [← metricSecond_coordinate_identity, plainEnergy_metricCoordinates,
    plainEnergy_metricCoordinates,plainEnergy_metricCoordinates] at hb
  have hn := metricNorm_nonneg (weightedSecond a u v)
  have hu := metricNorm_nonneg u
  have hv := metricNorm_nonneg v
  have hs := metricNorm_sq (weightedSecond a u v)
  have hsu := metricNorm_sq u
  have hsv := metricNorm_sq v
  nlinarith [mul_nonneg hu hv]

theorem weightedField_second_metric_bound {a : WeightedState} (ha : a∈weightedTube)
    (u v : WeightedState) :
    metricNorm (fderiv ℝ (fderiv ℝ weightedField) a u v)≤3*metricNorm u*metricNorm v := by
  rw [weightedField_second_fderiv_apply]
  exact weightedSecond_metric_bound ha u v

lemma metricEnergy_smul (c : ℝ) (u : WeightedState) :
    metricEnergy (c • u)=c^2*metricEnergy u := by
  simp [metricEnergy,smul_eq_mul]
  ring

lemma metricNorm_smul_nonneg (c : ℝ) (hc : 0≤c) (u : WeightedState) :
    metricNorm (c • u)=c*metricNorm u := by
  unfold metricNorm
  rw [metricEnergy_smul,Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq_eq_abs,abs_of_nonneg hc]

lemma weightedField_midpoint_second (x y : WeightedState) :
    (1/2:ℝ) • (weightedField x+weightedField y)-weightedField ((1/2:ℝ) • (x+y))=
      (1/8:ℝ) • weightedSecond ((1/2:ℝ) • (x+y)) (x-y) (x-y) := by
  ext i
  fin_cases i <;> simp [weightedField,weightedSecond,weightedBilinear,smul_eq_mul] <;> ring

/-- Exact cubic midpoint cancellation, followed by the metric Hessian bound. -/
theorem weightedField_midpoint_metric_bound {x y : WeightedState}
    (hx : x∈weightedTube) (hy : y∈weightedTube) :
    metricNorm ((1/2:ℝ) • (weightedField x+weightedField y)-
      weightedField ((1/2:ℝ) • (x+y)))≤(3/8)*(metricNorm (x-y))^2 := by
  have hm : (1/2:ℝ) • (x+y)∈weightedTube := by
    simpa only [smul_add] using weightedTube_convex hx hy
      (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  rw [weightedField_midpoint_second,metricNorm_smul_nonneg _ (by norm_num)]
  nlinarith [weightedSecond_metric_bound hm (x-y) (x-y)]

end
end CentroidEscape.MetricStability

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
  logInfo m!"Metric Hessian audit passed: {checked} declarations; standard axioms only."
