module
public import SolitonClassification.Rotating.FullGridPJoin2_8
public import SolitonClassification.Rotating.FullGridPJoin2_9
public import SolitonClassification.Rotating.FullGridPSeam3_4

@[expose] public section

namespace SolitonClassification.Rotating.FullGridPJoin3_4
open Candidate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem state_seam : FullGridPJoin2_8.certificate.state 256=FullGridPJoin2_9.certificate.state 0 := by
  rw [FullGridPJoin2_8.state_last,FullGridPJoin2_9.state_start]; exact FullGridPSeam3_4.state_equal
theorem matrix_seam : FullGridPJoin2_8.certificate.matrix 256=FullGridPJoin2_9.certificate.matrix 0 := by
  rw [FullGridPJoin2_8.matrix_last,FullGridPJoin2_9.matrix_start]; exact FullGridPSeam3_4.operator_equal
def certificate : PolynomialPointGridBlock (1:ℝ) (step:ℝ) (1/10^55) (1/10^55) 512 :=
  PolynomialPointGridBlock.append FullGridPJoin2_8.certificate FullGridPJoin2_9.certificate state_seam matrix_seam
theorem state_start : certificate.state 0=RP2048B00Nodes.state 0 := by
  rw [certificate,PolynomialPointGridBlock.append_state_zero,FullGridPJoin2_8.state_start]
theorem matrix_start : certificate.matrix 0=RP2048B00Nodes.operator 0 := by
  rw [certificate,PolynomialPointGridBlock.append_matrix_zero,FullGridPJoin2_8.matrix_start]
theorem state_last : certificate.state 512=RP2528B03Nodes.state 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).state (256+256)=_
  rw [PolynomialPointGridBlock.append_state_last,FullGridPJoin2_9.state_last]
theorem matrix_last : certificate.matrix 512=RP2528B03Nodes.operator 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).matrix (256+256)=_
  rw [PolynomialPointGridBlock.append_matrix_last,FullGridPJoin2_9.matrix_last]
attribute [irreducible] certificate

end
end SolitonClassification.Rotating.FullGridPJoin3_4

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
  logInfo m!"GridAssembly_FullGridPJoin3_4: {count} declarations; standard axioms only."
