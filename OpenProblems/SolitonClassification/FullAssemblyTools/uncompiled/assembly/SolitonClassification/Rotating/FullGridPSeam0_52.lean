module
public import SolitonClassification.Rotating.RP3328B03Nodes
public import SolitonClassification.Rotating.RP3360B00Nodes

@[expose] public section

namespace SolitonClassification.Rotating.FullGridPSeam0_52
open Candidate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem centers_equal : RP3328B03Nodes.centers 8=RP3360B00Nodes.centers 0 := by
  funext i; fin_cases i <;> decide +kernel
theorem matrices_equal : RP3328B03Nodes.matrix 8=RP3360B00Nodes.matrix 0 := by
  funext c i; fin_cases c <;> fin_cases i <;> decide +kernel
theorem state_equal : RP3328B03Nodes.state 8=RP3360B00Nodes.state 0 := by
  funext i
  change (((RP3328B03Nodes.centers 8 i:ℚ)/mesh:ℚ):ℝ)=(((RP3360B00Nodes.centers 0 i:ℚ)/mesh:ℚ):ℝ)
  rw [centers_equal]
theorem operator_equal : RP3328B03Nodes.operator 8=RP3360B00Nodes.operator 0 := by
  exact congrArg (pointMatrixOperator mesh) matrices_equal

end
end SolitonClassification.Rotating.FullGridPSeam0_52

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
  logInfo m!"GridAssembly_FullGridPSeam0_52: {count} declarations; standard axioms only."
