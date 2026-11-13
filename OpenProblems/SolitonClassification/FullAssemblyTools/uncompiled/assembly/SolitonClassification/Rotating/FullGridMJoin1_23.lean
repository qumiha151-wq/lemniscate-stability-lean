module
public import SolitonClassification.Rotating.FullGridMJoin0_46
public import SolitonClassification.Rotating.FullGridMJoin0_47
public import SolitonClassification.Rotating.FullGridMSeam1_23

@[expose] public section

namespace SolitonClassification.Rotating.FullGridMJoin1_23
open Candidate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem state_seam : FullGridMJoin0_46.certificate.state 64=FullGridMJoin0_47.certificate.state 0 := by
  rw [FullGridMJoin0_46.state_last,FullGridMJoin0_47.state_start]; exact FullGridMSeam1_23.state_equal
theorem matrix_seam : FullGridMJoin0_46.certificate.matrix 64=FullGridMJoin0_47.certificate.matrix 0 := by
  rw [FullGridMJoin0_46.matrix_last,FullGridMJoin0_47.matrix_start]; exact FullGridMSeam1_23.operator_equal
def certificate : PolynomialPointGridBlock (-1:ℝ) (step:ℝ) (1/10^55) (1/10^55) 128 :=
  PolynomialPointGridBlock.append FullGridMJoin0_46.certificate FullGridMJoin0_47.certificate state_seam matrix_seam
theorem state_start : certificate.state 0=RM2944B00Nodes.state 0 := by
  rw [certificate,PolynomialPointGridBlock.append_state_zero,FullGridMJoin0_46.state_start]
theorem matrix_start : certificate.matrix 0=RM2944B00Nodes.operator 0 := by
  rw [certificate,PolynomialPointGridBlock.append_matrix_zero,FullGridMJoin0_46.matrix_start]
theorem state_last : certificate.state 128=RM3040B03Nodes.state 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).state (64+64)=_
  rw [PolynomialPointGridBlock.append_state_last,FullGridMJoin0_47.state_last]
theorem matrix_last : certificate.matrix 128=RM3040B03Nodes.operator 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).matrix (64+64)=_
  rw [PolynomialPointGridBlock.append_matrix_last,FullGridMJoin0_47.matrix_last]
attribute [irreducible] certificate

end
end SolitonClassification.Rotating.FullGridMJoin1_23

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
  logInfo m!"GridAssembly_FullGridMJoin1_23: {count} declarations; standard axioms only."
