module
public import SolitonClassification.Rotating.RM1472Join1_0
public import SolitonClassification.Rotating.RM1504Join1_0
public import SolitonClassification.Rotating.FullGridMSeam0_23

@[expose] public section

namespace SolitonClassification.Rotating.FullGridMJoin0_23
open Candidate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem state_seam : RM1472Join1_0.certificate.state 32=RM1504Join1_0.certificate.state 0 := by
  rw [RM1472Join1_0.state_last,RM1504Join1_0.state_start]; exact FullGridMSeam0_23.state_equal
theorem matrix_seam : RM1472Join1_0.certificate.matrix 32=RM1504Join1_0.certificate.matrix 0 := by
  rw [RM1472Join1_0.matrix_last,RM1504Join1_0.matrix_start]; exact FullGridMSeam0_23.operator_equal
def certificate : PolynomialPointGridBlock (-1:ℝ) (step:ℝ) (1/10^55) (1/10^55) 64 :=
  PolynomialPointGridBlock.append RM1472Join1_0.certificate RM1504Join1_0.certificate state_seam matrix_seam
theorem state_start : certificate.state 0=RM1472B00Nodes.state 0 := by
  rw [certificate,PolynomialPointGridBlock.append_state_zero,RM1472Join1_0.state_start]
theorem matrix_start : certificate.matrix 0=RM1472B00Nodes.operator 0 := by
  rw [certificate,PolynomialPointGridBlock.append_matrix_zero,RM1472Join1_0.matrix_start]
theorem state_last : certificate.state 64=RM1504B03Nodes.state 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).state (32+32)=_
  rw [PolynomialPointGridBlock.append_state_last,RM1504Join1_0.state_last]
theorem matrix_last : certificate.matrix 64=RM1504B03Nodes.operator 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).matrix (32+32)=_
  rw [PolynomialPointGridBlock.append_matrix_last,RM1504Join1_0.matrix_last]
attribute [irreducible] certificate

end
end SolitonClassification.Rotating.FullGridMJoin0_23

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
  logInfo m!"GridAssembly_FullGridMJoin0_23: {count} declarations; standard axioms only."
