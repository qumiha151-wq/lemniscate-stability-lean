import SolitonClassification.Rotating.Grid42P00Matrix
import SolitonClassification.Rotating.UniversalReducedVariation

/-! A first actual42/22 segment from independently stored node data.
This imports no previous numeric coefficient table. The universal tail
uses state42 and the genuine mixed42/22 variational residual. -/
namespace SolitonClassification.Rotating.Grid42P00Actual
noncomputable section
open Set Candidate UniversalMajorant Grid42P00Nodes
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

theorem initial_bounds_checked : |rawInitial 0|≤407/50 ∧ |rawInitial 1|≤33/8 ∧
    |rawInitial 2|≤731/100 ∧ |rawInitial 3|≤731/100 ∧ |rawInitial 4|≤1/100 := by decide +kernel

theorem initial_inner : initial∈innerTube := by
  have lift (q r : ℚ) (h : |q|≤r) : |(q:ℝ)|≤(r:ℝ) := by
    rw [←Rat.cast_abs]
    exact Rat.cast_le.mpr h
  rcases initial_bounds_checked with ⟨h0,h1,h2,h3,h4⟩
  change |(rawInitial 0:ℝ)|≤407/50 ∧ |(rawInitial 1:ℝ)|≤33/8 ∧
    |(rawInitial 2:ℝ)|≤731/100 ∧ |(rawInitial 3:ℝ)|≤731/100 ∧ |(rawInitial 4:ℝ)|≤1/100
  exact ⟨by simpa only [Rat.cast_div,Rat.cast_ofNat] using lift _ _ h0,
    by simpa only [Rat.cast_div,Rat.cast_ofNat] using lift _ _ h1,
    by simpa only [Rat.cast_div,Rat.cast_ofNat] using lift _ _ h2,
    by simpa only [Rat.cast_div,Rat.cast_ofNat] using lift _ _ h3,
    by simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using lift _ _ h4⟩

theorem step_mem : (step:ℝ)∈Icc 0 (universalStepCap:ℝ) :=
  ⟨Rat.cast_nonneg.mpr positive_step.le,Rat.cast_le.mpr step_below_cap.le⟩

theorem actual_original_ODE {t : ℝ} (ht : t∈Icc 0 (step:ℝ)) :
    HasDerivAt (fun s=>supportFlow 1 (by norm_num) s initial)
      (field (supportFlow 1 (by norm_num) t initial)) t := by
  simpa only [one_smul] using supportFlow_short_original 1 (by norm_num) initial_inner ht.1
    (ht.2.trans (step_mem.2.trans universalStepCap_le_local))

theorem actual_state_endpoint :
    ‖supportFlow 1 (by norm_num) (step:ℝ) initial-nextState‖≤2/10^41 := by
  have ht:=universal_signed_trueTaylor42_error 1 (by norm_num) initial_inner step_mem
  simp only [one_mul] at ht
  have hr:=Grid42P00State.state_reset
  have htri:=dist_triangle (supportFlow 1 (by norm_num) (step:ℝ) initial)
    (polynomialPath (taylorPolynomial initial 42) (step:ℝ)) nextState
  simp only [dist_eq_norm] at htri
  exact htri.trans ((add_le_add ht hr).trans (by norm_num))

theorem actual_matrix_endpoint :
    ‖fderiv ℝ (supportFlow 1 (by norm_num) (step:ℝ)) initial-nextOperator‖≤5/10^21 := by
  have ht:=universal_signed_trueVariation42_22_operator_error 1 (by norm_num) initial_inner step_mem
  simp only [one_mul] at ht
  have hr:=Grid42P00Matrix.matrix_reset
  rw [start_identity] at hr
  change ‖(variationPolynomialMap initial 22 (step:ℝ))*1-nextOperator‖≤(1:ℝ)/10^57 at hr
  rw [mul_one] at hr
  have htri:=dist_triangle (fderiv ℝ (supportFlow 1 (by norm_num) (step:ℝ)) initial)
    (variationPolynomialMap initial 22 (step:ℝ)) nextOperator
  simp only [dist_eq_norm] at htri
  exact htri.trans ((add_le_add ht hr).trans (by norm_num))

end
end SolitonClassification.Rotating.Grid42P00Actual

#print axioms SolitonClassification.Rotating.Grid42P00Actual.actual_state_endpoint
#print axioms SolitonClassification.Rotating.Grid42P00Actual.actual_matrix_endpoint
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Independent first actual42/22 segment audited: {count} declarations, standard axioms only."
