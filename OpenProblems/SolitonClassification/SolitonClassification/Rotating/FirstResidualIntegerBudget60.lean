import SolitonClassification.Rotating.FirstResidualIntegerRanks60
namespace SolitonClassification.Rotating.FirstResidualInteger60
open Candidate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false


theorem tube_integer_checked : ∀i : Fin 6,
  integerEnvelopeNumerator (fun n=>BenchState60.table.coefficient n i) 100 60≤tubeThresholds i := by decide +kernel

theorem residual_integer_checked : ∀i : Fin 6,
  integerEnvelopeNumerator (fun n=>residualDataValue 60 residuals n i) 100 180≤(10:ℤ)^340 := by decide +kernel

theorem tube_quotient_checked : ∀i : Fin 6,
  (tubeThresholds i:ℚ)/((mesh:ℚ)*100^60)≤tubeLimits i := by decide +kernel

theorem residual_quotient_checked : ((10:ℤ)^340:ℚ)/((mesh:ℚ)*100^180)≤1/10^80 := by decide +kernel

theorem tube_budget_checked (i : Fin 6) :
  rationalEnvelope (fun n=>fixedAbsUpper mesh (BenchState60.table.coefficient n i)) budgetTime 60≤tubeLimits i :=
  fixedEnvelope_le_of_integer_check _ mesh_pos (by norm_num) (tube_integer_checked i) (tube_quotient_checked i)

theorem residual_budget_checked (i : Fin 6) :
  rationalEnvelope (fun n=>fixedAbsUpper mesh (residualDataValue 60 residuals n i)) budgetTime 180≤1/10^80 :=
  fixedEnvelope_le_of_integer_check _ mesh_pos (by norm_num) (residual_integer_checked i) residual_quotient_checked

theorem actual_polynomial_tube {t : ℝ} (ht : |t|≤(budgetTime:ℝ)) :
    polynomialPath (taylorPolynomial initial 60) t∈outerTube := by
  have h (i : Fin 6) : |(taylorPolynomial initial 60 i).eval t|≤(tubeLimits i:ℝ) := by
    have hc : ∀n≤60,|(taylorPolynomial initial 60 i).coeff n|≤
        (fixedAbsUpper mesh (BenchState60.table.coefficient n i):ℝ) := by
      intro n hn
      exact fixedAbsUpper_sound (state_sound.polynomialCoefficient n i)
    exact (finitePolynomial_abs_bound (taylorPolynomial_degree initial 60 i) hc ht).trans
      (by exact_mod_cast tube_budget_checked i)
  have h0:=h 0;have h1:=h 1;have h2:=h 2;have h3:=h 3;have h4:=h 4
  change |(taylorPolynomial initial 60 0).eval t|≤(17/2:ℚ) at h0
  change |(taylorPolynomial initial 60 1).eval t|≤(9/2:ℚ) at h1
  change |(taylorPolynomial initial 60 2).eval t|≤(17/2:ℚ) at h2
  change |(taylorPolynomial initial 60 3).eval t|≤(17/2:ℚ) at h3
  change |(taylorPolynomial initial 60 4).eval t|≤(1/50:ℚ) at h4
  norm_num at h0 h1 h2 h3 h4
  exact ⟨h0,h1,h2,h3,h4⟩

theorem actual_residual_bound {t : ℝ} (ht : |t|≤(budgetTime:ℝ)) :
    ‖polynomialPath (taylorResidual initial 60) t‖≤(1:ℝ)/10^80 := by
  have h:=certifiedState_residual_bound mesh_pos state_sound squares_checked residuals_checked
    (show (0:ℚ)≤1/10^80 by norm_num) residual_budget_checked ht
  norm_num at h ⊢
  exact h

#print axioms SolitonClassification.Rotating.FirstResidualInteger60.actual_residual_bound


end SolitonClassification.Rotating.FirstResidualInteger60
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Concrete integer whole-segment residual audit passed."
