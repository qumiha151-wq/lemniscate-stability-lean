module
public import SolitonClassification.Rotating.FullGridMJoin2_2
public import SolitonClassification.Rotating.FullGridMJoin2_3
public import SolitonClassification.Rotating.FullGridMSeam3_1

@[expose] public section

namespace SolitonClassification.Rotating.FullGridMJoin3_1
open Candidate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem state_seam : FullGridMJoin2_2.certificate.state 256=FullGridMJoin2_3.certificate.state 0 := by
  rw [FullGridMJoin2_2.state_last,FullGridMJoin2_3.state_start]; exact FullGridMSeam3_1.state_equal
theorem matrix_seam : FullGridMJoin2_2.certificate.matrix 256=FullGridMJoin2_3.certificate.matrix 0 := by
  rw [FullGridMJoin2_2.matrix_last,FullGridMJoin2_3.matrix_start]; exact FullGridMSeam3_1.operator_equal
def certificate : PolynomialPointGridBlock (-1:ℝ) (step:ℝ) (1/10^55) (1/10^55) 512 :=
  PolynomialPointGridBlock.append FullGridMJoin2_2.certificate FullGridMJoin2_3.certificate state_seam matrix_seam
theorem state_start : certificate.state 0=RM0512B00Nodes.state 0 := by
  rw [certificate,PolynomialPointGridBlock.append_state_zero,FullGridMJoin2_2.state_start]
theorem matrix_start : certificate.matrix 0=RM0512B00Nodes.operator 0 := by
  rw [certificate,PolynomialPointGridBlock.append_matrix_zero,FullGridMJoin2_2.matrix_start]
theorem state_last : certificate.state 512=RM0992B03Nodes.state 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).state (256+256)=_
  rw [PolynomialPointGridBlock.append_state_last,FullGridMJoin2_3.state_last]
theorem matrix_last : certificate.matrix 512=RM0992B03Nodes.operator 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).matrix (256+256)=_
  rw [PolynomialPointGridBlock.append_matrix_last,FullGridMJoin2_3.matrix_last]
attribute [irreducible] certificate

end
end SolitonClassification.Rotating.FullGridMJoin3_1

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
  logInfo m!"GridAssembly_FullGridMJoin3_1: {count} declarations; standard axioms only."
