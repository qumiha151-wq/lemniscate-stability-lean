module
public import SolitonClassification.Rotating.RM1472B03Nodes
public import SolitonClassification.Rotating.RM1504B00Nodes

@[expose] public section

namespace SolitonClassification.Rotating.FullGridMSeam0_23
open Candidate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem centers_equal : RM1472B03Nodes.centers 8=RM1504B00Nodes.centers 0 := by
  funext i; fin_cases i <;> decide +kernel
theorem matrices_equal : RM1472B03Nodes.matrix 8=RM1504B00Nodes.matrix 0 := by
  funext c i; fin_cases c <;> fin_cases i <;> decide +kernel
theorem state_equal : RM1472B03Nodes.state 8=RM1504B00Nodes.state 0 := by
  funext i
  change (((RM1472B03Nodes.centers 8 i:ℚ)/mesh:ℚ):ℝ)=(((RM1504B00Nodes.centers 0 i:ℚ)/mesh:ℚ):ℝ)
  rw [centers_equal]
theorem operator_equal : RM1472B03Nodes.operator 8=RM1504B00Nodes.operator 0 := by
  exact congrArg (pointMatrixOperator mesh) matrices_equal

end
end SolitonClassification.Rotating.FullGridMSeam0_23

end

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf (privateToUserName name) then
      for ax in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Grid assembly audit failed: {name} depends on {ax}"
      count := count + 1
  logInfo m!"GridAssembly_FullGridMSeam0_23: {count} declarations; standard axioms only."
