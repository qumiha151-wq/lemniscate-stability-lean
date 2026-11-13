module
public import SolitonClassification.Rotating.FullGridPJoin3_6
public import SolitonClassification.Rotating.FullGridPJoin3_7
public import SolitonClassification.Rotating.FullGridPSeam4_3

@[expose] public section

namespace SolitonClassification.Rotating.FullGridPJoin4_3
open Candidate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem state_seam : FullGridPJoin3_6.certificate.state 512=FullGridPJoin3_7.certificate.state 0 := by
  rw [FullGridPJoin3_6.state_last,FullGridPJoin3_7.state_start]; exact FullGridPSeam4_3.state_equal
theorem matrix_seam : FullGridPJoin3_6.certificate.matrix 512=FullGridPJoin3_7.certificate.matrix 0 := by
  rw [FullGridPJoin3_6.matrix_last,FullGridPJoin3_7.matrix_start]; exact FullGridPSeam4_3.operator_equal
def certificate : PolynomialPointGridBlock (1:ℝ) (step:ℝ) (1/10^55) (1/10^55) 928 :=
  PolynomialPointGridBlock.append FullGridPJoin3_6.certificate FullGridPJoin3_7.certificate state_seam matrix_seam
theorem state_start : certificate.state 0=RP3072B00Nodes.state 0 := by
  rw [certificate,PolynomialPointGridBlock.append_state_zero,FullGridPJoin3_6.state_start]
theorem matrix_start : certificate.matrix 0=RP3072B00Nodes.operator 0 := by
  rw [certificate,PolynomialPointGridBlock.append_matrix_zero,FullGridPJoin3_6.matrix_start]
theorem state_last : certificate.state 928=RP3968B03Nodes.state 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).state (512+416)=_
  rw [PolynomialPointGridBlock.append_state_last,FullGridPJoin3_7.state_last]
theorem matrix_last : certificate.matrix 928=RP3968B03Nodes.operator 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).matrix (512+416)=_
  rw [PolynomialPointGridBlock.append_matrix_last,FullGridPJoin3_7.matrix_last]
attribute [irreducible] certificate

end
end SolitonClassification.Rotating.FullGridPJoin4_3

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
  logInfo m!"GridAssembly_FullGridPJoin4_3: {count} declarations; standard axioms only."
