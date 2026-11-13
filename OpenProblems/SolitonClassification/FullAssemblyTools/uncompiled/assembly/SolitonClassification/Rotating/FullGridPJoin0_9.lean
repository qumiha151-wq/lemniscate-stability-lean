module
public import SolitonClassification.Rotating.RP0576Join1_0
public import SolitonClassification.Rotating.RP0608Join1_0
public import SolitonClassification.Rotating.FullGridPSeam0_9

@[expose] public section

namespace SolitonClassification.Rotating.FullGridPJoin0_9
open Candidate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem state_seam : RP0576Join1_0.certificate.state 32=RP0608Join1_0.certificate.state 0 := by
  rw [RP0576Join1_0.state_last,RP0608Join1_0.state_start]; exact FullGridPSeam0_9.state_equal
theorem matrix_seam : RP0576Join1_0.certificate.matrix 32=RP0608Join1_0.certificate.matrix 0 := by
  rw [RP0576Join1_0.matrix_last,RP0608Join1_0.matrix_start]; exact FullGridPSeam0_9.operator_equal
def certificate : PolynomialPointGridBlock (1:ℝ) (step:ℝ) (1/10^55) (1/10^55) 64 :=
  PolynomialPointGridBlock.append RP0576Join1_0.certificate RP0608Join1_0.certificate state_seam matrix_seam
theorem state_start : certificate.state 0=RP0576B00Nodes.state 0 := by
  rw [certificate,PolynomialPointGridBlock.append_state_zero,RP0576Join1_0.state_start]
theorem matrix_start : certificate.matrix 0=RP0576B00Nodes.operator 0 := by
  rw [certificate,PolynomialPointGridBlock.append_matrix_zero,RP0576Join1_0.matrix_start]
theorem state_last : certificate.state 64=RP0608B03Nodes.state 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).state (32+32)=_
  rw [PolynomialPointGridBlock.append_state_last,RP0608Join1_0.state_last]
theorem matrix_last : certificate.matrix 64=RP0608B03Nodes.operator 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).matrix (32+32)=_
  rw [PolynomialPointGridBlock.append_matrix_last,RP0608Join1_0.matrix_last]
attribute [irreducible] certificate

end
end SolitonClassification.Rotating.FullGridPJoin0_9

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
  logInfo m!"GridAssembly_FullGridPJoin0_9: {count} declarations; standard axioms only."
