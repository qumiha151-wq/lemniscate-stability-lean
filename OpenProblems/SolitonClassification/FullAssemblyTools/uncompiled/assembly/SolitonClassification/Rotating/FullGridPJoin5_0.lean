module
public import SolitonClassification.Rotating.FullGridPJoin4_0
public import SolitonClassification.Rotating.FullGridPJoin4_1
public import SolitonClassification.Rotating.FullGridPSeam5_0

@[expose] public section

namespace SolitonClassification.Rotating.FullGridPJoin5_0
open Candidate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem state_seam : FullGridPJoin4_0.certificate.state 1024=FullGridPJoin4_1.certificate.state 0 := by
  rw [FullGridPJoin4_0.state_last,FullGridPJoin4_1.state_start]; exact FullGridPSeam5_0.state_equal
theorem matrix_seam : FullGridPJoin4_0.certificate.matrix 1024=FullGridPJoin4_1.certificate.matrix 0 := by
  rw [FullGridPJoin4_0.matrix_last,FullGridPJoin4_1.matrix_start]; exact FullGridPSeam5_0.operator_equal
def certificate : PolynomialPointGridBlock (1:ℝ) (step:ℝ) (1/10^55) (1/10^55) 2048 :=
  PolynomialPointGridBlock.append FullGridPJoin4_0.certificate FullGridPJoin4_1.certificate state_seam matrix_seam
theorem state_start : certificate.state 0=RP0000B00Nodes.state 0 := by
  rw [certificate,PolynomialPointGridBlock.append_state_zero,FullGridPJoin4_0.state_start]
theorem matrix_start : certificate.matrix 0=RP0000B00Nodes.operator 0 := by
  rw [certificate,PolynomialPointGridBlock.append_matrix_zero,FullGridPJoin4_0.matrix_start]
theorem state_last : certificate.state 2048=RP2016B03Nodes.state 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).state (1024+1024)=_
  rw [PolynomialPointGridBlock.append_state_last,FullGridPJoin4_1.state_last]
theorem matrix_last : certificate.matrix 2048=RP2016B03Nodes.operator 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).matrix (1024+1024)=_
  rw [PolynomialPointGridBlock.append_matrix_last,FullGridPJoin4_1.matrix_last]
attribute [irreducible] certificate

end
end SolitonClassification.Rotating.FullGridPJoin5_0

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
  logInfo m!"GridAssembly_FullGridPJoin5_0: {count} declarations; standard axioms only."
