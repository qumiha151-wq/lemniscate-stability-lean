module

public import SolitonClassification.Rotating.Field
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! Conversion from all six checked columns to the actual supremum operator
norm. A uniform column error ε costs a factor six; it is never silently
identified with operator error ε. The nonuniform sum bound is also retained. -/
namespace SolitonClassification.Rotating
noncomputable section
open Finset
set_option Elab.async false

def coordinateBasis (j : Fin 6) : State := fun i=>if i=j then 1 else 0

def columnOperator (W : Fin 6 → State) : State →L[ℝ] State :=
  ∑j : Fin 6,(ContinuousLinearMap.proj j).smulRight (W j)

theorem columnOperator_apply (W : Fin 6 → State) (x : State) :
    columnOperator W x=∑j : Fin 6,x j • W j := by
  simp [columnOperator]

theorem columnOperator_basis (W : Fin 6 → State) (j : Fin 6) :
    columnOperator W (coordinateBasis j)=W j := by
  simp [columnOperator_apply,coordinateBasis]

theorem state_basis_expansion (x : State) :
    x=∑j : Fin 6,x j • coordinateBasis j := by
  ext i
  simp [coordinateBasis]

theorem operator_norm_le_column_sum (L : State →L[ℝ] State) :
    ‖L‖≤∑j : Fin 6,‖L (coordinateBasis j)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _=>norm_nonneg _)
  intro x
  calc
    ‖L x‖ = ‖∑j : Fin 6,x j • L (coordinateBasis j)‖ := by
      conv_lhs => rw [state_basis_expansion x]
      simp only [map_sum,map_smul]
    _ ≤ ∑j : Fin 6,‖x j • L (coordinateBasis j)‖ := norm_sum_le _ _
    _ ≤ ∑j : Fin 6,‖x‖*‖L (coordinateBasis j)‖ := by
      apply sum_le_sum
      intro j _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (norm_le_pi_norm x j) (norm_nonneg _)
    _ = (∑j : Fin 6,‖L (coordinateBasis j)‖)*‖x‖ := by rw [←mul_sum,mul_comm]

theorem operator_norm_le_six_column_bound (L : State →L[ℝ] State) {ε : ℝ}
    (h : ∀j : Fin 6,‖L (coordinateBasis j)‖≤ε) : ‖L‖≤6*ε := by
  apply operator_norm_le_column_sum L |>.trans
  calc
    _ ≤ ∑_j : Fin 6,ε := sum_le_sum fun j _=>h j
    _ = _ := by simp

theorem operator_difference_le_six_column_bound (A B : State →L[ℝ] State) {ε : ℝ}
    (h : ∀j : Fin 6,‖A (coordinateBasis j)-B (coordinateBasis j)‖≤ε) :
    ‖A-B‖≤6*ε := operator_norm_le_six_column_bound (A-B) h

theorem operator_error_of_columns (A : State →L[ℝ] State) (W : Fin 6 → State) {ε : ℝ}
    (h : ∀j : Fin 6,‖A (coordinateBasis j)-W j‖≤ε) :
    ‖A-columnOperator W‖≤6*ε := by
  apply operator_difference_le_six_column_bound
  simpa only [columnOperator_basis] using h

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.operator_difference_le_six_column_bound
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Full six-column operator-norm conversion audit passed."

end
