module
public import SolitonClassification.Rotating.FullGridPJoin1_24
public import SolitonClassification.Rotating.FullGridPJoin1_25
public import SolitonClassification.Rotating.FullGridPSeam2_12

@[expose] public section

namespace SolitonClassification.Rotating.FullGridPJoin2_12
open Candidate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem state_seam : FullGridPJoin1_24.certificate.state 128=FullGridPJoin1_25.certificate.state 0 := by
  rw [FullGridPJoin1_24.state_last,FullGridPJoin1_25.state_start]; exact FullGridPSeam2_12.state_equal
theorem matrix_seam : FullGridPJoin1_24.certificate.matrix 128=FullGridPJoin1_25.certificate.matrix 0 := by
  rw [FullGridPJoin1_24.matrix_last,FullGridPJoin1_25.matrix_start]; exact FullGridPSeam2_12.operator_equal
def certificate : PolynomialPointGridBlock (1:ℝ) (step:ℝ) (1/10^55) (1/10^55) 256 :=
  PolynomialPointGridBlock.append FullGridPJoin1_24.certificate FullGridPJoin1_25.certificate state_seam matrix_seam
theorem state_start : certificate.state 0=RP3072B00Nodes.state 0 := by
  rw [certificate,PolynomialPointGridBlock.append_state_zero,FullGridPJoin1_24.state_start]
theorem matrix_start : certificate.matrix 0=RP3072B00Nodes.operator 0 := by
  rw [certificate,PolynomialPointGridBlock.append_matrix_zero,FullGridPJoin1_24.matrix_start]
theorem state_last : certificate.state 256=RP3296B03Nodes.state 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).state (128+128)=_
  rw [PolynomialPointGridBlock.append_state_last,FullGridPJoin1_25.state_last]
theorem matrix_last : certificate.matrix 256=RP3296B03Nodes.operator 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).matrix (128+128)=_
  rw [PolynomialPointGridBlock.append_matrix_last,FullGridPJoin1_25.matrix_last]
attribute [irreducible] certificate

end
end SolitonClassification.Rotating.FullGridPJoin2_12

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
  logInfo m!"GridAssembly_FullGridPJoin2_12: {count} declarations; standard axioms only."
