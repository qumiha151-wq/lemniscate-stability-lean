module
public import SolitonClassification.Rotating.RP3264Join1_0
public import SolitonClassification.Rotating.RP3296Join1_0
public import SolitonClassification.Rotating.FullGridPSeam0_51

@[expose] public section

namespace SolitonClassification.Rotating.FullGridPJoin0_51
open Candidate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem state_seam : RP3264Join1_0.certificate.state 32=RP3296Join1_0.certificate.state 0 := by
  rw [RP3264Join1_0.state_last,RP3296Join1_0.state_start]; exact FullGridPSeam0_51.state_equal
theorem matrix_seam : RP3264Join1_0.certificate.matrix 32=RP3296Join1_0.certificate.matrix 0 := by
  rw [RP3264Join1_0.matrix_last,RP3296Join1_0.matrix_start]; exact FullGridPSeam0_51.operator_equal
def certificate : PolynomialPointGridBlock (1:ℝ) (step:ℝ) (1/10^55) (1/10^55) 64 :=
  PolynomialPointGridBlock.append RP3264Join1_0.certificate RP3296Join1_0.certificate state_seam matrix_seam
theorem state_start : certificate.state 0=RP3264B00Nodes.state 0 := by
  rw [certificate,PolynomialPointGridBlock.append_state_zero,RP3264Join1_0.state_start]
theorem matrix_start : certificate.matrix 0=RP3264B00Nodes.operator 0 := by
  rw [certificate,PolynomialPointGridBlock.append_matrix_zero,RP3264Join1_0.matrix_start]
theorem state_last : certificate.state 64=RP3296B03Nodes.state 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).state (32+32)=_
  rw [PolynomialPointGridBlock.append_state_last,RP3296Join1_0.state_last]
theorem matrix_last : certificate.matrix 64=RP3296B03Nodes.operator 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).matrix (32+32)=_
  rw [PolynomialPointGridBlock.append_matrix_last,RP3296Join1_0.matrix_last]
attribute [irreducible] certificate

end
end SolitonClassification.Rotating.FullGridPJoin0_51

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
  logInfo m!"GridAssembly_FullGridPJoin0_51: {count} declarations; standard axioms only."
