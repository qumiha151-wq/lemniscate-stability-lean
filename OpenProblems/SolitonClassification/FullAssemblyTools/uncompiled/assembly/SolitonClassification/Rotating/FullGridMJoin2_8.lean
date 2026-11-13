module
public import SolitonClassification.Rotating.FullGridMJoin1_16
public import SolitonClassification.Rotating.FullGridMJoin1_17
public import SolitonClassification.Rotating.FullGridMSeam2_8

@[expose] public section

namespace SolitonClassification.Rotating.FullGridMJoin2_8
open Candidate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem state_seam : FullGridMJoin1_16.certificate.state 128=FullGridMJoin1_17.certificate.state 0 := by
  rw [FullGridMJoin1_16.state_last,FullGridMJoin1_17.state_start]; exact FullGridMSeam2_8.state_equal
theorem matrix_seam : FullGridMJoin1_16.certificate.matrix 128=FullGridMJoin1_17.certificate.matrix 0 := by
  rw [FullGridMJoin1_16.matrix_last,FullGridMJoin1_17.matrix_start]; exact FullGridMSeam2_8.operator_equal
def certificate : PolynomialPointGridBlock (-1:ℝ) (step:ℝ) (1/10^55) (1/10^55) 256 :=
  PolynomialPointGridBlock.append FullGridMJoin1_16.certificate FullGridMJoin1_17.certificate state_seam matrix_seam
theorem state_start : certificate.state 0=RM2048B00Nodes.state 0 := by
  rw [certificate,PolynomialPointGridBlock.append_state_zero,FullGridMJoin1_16.state_start]
theorem matrix_start : certificate.matrix 0=RM2048B00Nodes.operator 0 := by
  rw [certificate,PolynomialPointGridBlock.append_matrix_zero,FullGridMJoin1_16.matrix_start]
theorem state_last : certificate.state 256=RM2272B03Nodes.state 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).state (128+128)=_
  rw [PolynomialPointGridBlock.append_state_last,FullGridMJoin1_17.state_last]
theorem matrix_last : certificate.matrix 256=RM2272B03Nodes.operator 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).matrix (128+128)=_
  rw [PolynomialPointGridBlock.append_matrix_last,FullGridMJoin1_17.matrix_last]
attribute [irreducible] certificate

end
end SolitonClassification.Rotating.FullGridMJoin2_8

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
  logInfo m!"GridAssembly_FullGridMJoin2_8: {count} declarations; standard axioms only."
