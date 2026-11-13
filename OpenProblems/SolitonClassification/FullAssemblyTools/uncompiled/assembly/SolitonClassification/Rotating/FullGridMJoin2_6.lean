module
public import SolitonClassification.Rotating.FullGridMJoin1_12
public import SolitonClassification.Rotating.FullGridMJoin1_13
public import SolitonClassification.Rotating.FullGridMSeam2_6

@[expose] public section

namespace SolitonClassification.Rotating.FullGridMJoin2_6
open Candidate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem state_seam : FullGridMJoin1_12.certificate.state 128=FullGridMJoin1_13.certificate.state 0 := by
  rw [FullGridMJoin1_12.state_last,FullGridMJoin1_13.state_start]; exact FullGridMSeam2_6.state_equal
theorem matrix_seam : FullGridMJoin1_12.certificate.matrix 128=FullGridMJoin1_13.certificate.matrix 0 := by
  rw [FullGridMJoin1_12.matrix_last,FullGridMJoin1_13.matrix_start]; exact FullGridMSeam2_6.operator_equal
def certificate : PolynomialPointGridBlock (-1:ℝ) (step:ℝ) (1/10^55) (1/10^55) 256 :=
  PolynomialPointGridBlock.append FullGridMJoin1_12.certificate FullGridMJoin1_13.certificate state_seam matrix_seam
theorem state_start : certificate.state 0=RM1536B00Nodes.state 0 := by
  rw [certificate,PolynomialPointGridBlock.append_state_zero,FullGridMJoin1_12.state_start]
theorem matrix_start : certificate.matrix 0=RM1536B00Nodes.operator 0 := by
  rw [certificate,PolynomialPointGridBlock.append_matrix_zero,FullGridMJoin1_12.matrix_start]
theorem state_last : certificate.state 256=RM1760B03Nodes.state 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).state (128+128)=_
  rw [PolynomialPointGridBlock.append_state_last,FullGridMJoin1_13.state_last]
theorem matrix_last : certificate.matrix 256=RM1760B03Nodes.operator 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).matrix (128+128)=_
  rw [PolynomialPointGridBlock.append_matrix_last,FullGridMJoin1_13.matrix_last]
attribute [irreducible] certificate

end
end SolitonClassification.Rotating.FullGridMJoin2_6

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
  logInfo m!"GridAssembly_FullGridMJoin2_6: {count} declarations; standard axioms only."
