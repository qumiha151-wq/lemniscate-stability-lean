module
public import SolitonClassification.Rotating.FullGridPJoin0_18
public import SolitonClassification.Rotating.FullGridPJoin0_19
public import SolitonClassification.Rotating.FullGridPSeam1_9

@[expose] public section

namespace SolitonClassification.Rotating.FullGridPJoin1_9
open Candidate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem state_seam : FullGridPJoin0_18.certificate.state 64=FullGridPJoin0_19.certificate.state 0 := by
  rw [FullGridPJoin0_18.state_last,FullGridPJoin0_19.state_start]; exact FullGridPSeam1_9.state_equal
theorem matrix_seam : FullGridPJoin0_18.certificate.matrix 64=FullGridPJoin0_19.certificate.matrix 0 := by
  rw [FullGridPJoin0_18.matrix_last,FullGridPJoin0_19.matrix_start]; exact FullGridPSeam1_9.operator_equal
def certificate : PolynomialPointGridBlock (1:ℝ) (step:ℝ) (1/10^55) (1/10^55) 128 :=
  PolynomialPointGridBlock.append FullGridPJoin0_18.certificate FullGridPJoin0_19.certificate state_seam matrix_seam
theorem state_start : certificate.state 0=RP1152B00Nodes.state 0 := by
  rw [certificate,PolynomialPointGridBlock.append_state_zero,FullGridPJoin0_18.state_start]
theorem matrix_start : certificate.matrix 0=RP1152B00Nodes.operator 0 := by
  rw [certificate,PolynomialPointGridBlock.append_matrix_zero,FullGridPJoin0_18.matrix_start]
theorem state_last : certificate.state 128=RP1248B03Nodes.state 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).state (64+64)=_
  rw [PolynomialPointGridBlock.append_state_last,FullGridPJoin0_19.state_last]
theorem matrix_last : certificate.matrix 128=RP1248B03Nodes.operator 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).matrix (64+64)=_
  rw [PolynomialPointGridBlock.append_matrix_last,FullGridPJoin0_19.matrix_last]
attribute [irreducible] certificate

end
end SolitonClassification.Rotating.FullGridPJoin1_9

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
  logInfo m!"GridAssembly_FullGridPJoin1_9: {count} declarations; standard axioms only."
