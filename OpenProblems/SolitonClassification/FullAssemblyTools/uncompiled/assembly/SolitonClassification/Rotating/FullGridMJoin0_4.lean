module
public import SolitonClassification.Rotating.RM0256Join1_0
public import SolitonClassification.Rotating.RM0288Join1_0
public import SolitonClassification.Rotating.FullGridMSeam0_4

@[expose] public section

namespace SolitonClassification.Rotating.FullGridMJoin0_4
open Candidate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem state_seam : RM0256Join1_0.certificate.state 32=RM0288Join1_0.certificate.state 0 := by
  rw [RM0256Join1_0.state_last,RM0288Join1_0.state_start]; exact FullGridMSeam0_4.state_equal
theorem matrix_seam : RM0256Join1_0.certificate.matrix 32=RM0288Join1_0.certificate.matrix 0 := by
  rw [RM0256Join1_0.matrix_last,RM0288Join1_0.matrix_start]; exact FullGridMSeam0_4.operator_equal
def certificate : PolynomialPointGridBlock (-1:ℝ) (step:ℝ) (1/10^55) (1/10^55) 64 :=
  PolynomialPointGridBlock.append RM0256Join1_0.certificate RM0288Join1_0.certificate state_seam matrix_seam
theorem state_start : certificate.state 0=RM0256B00Nodes.state 0 := by
  rw [certificate,PolynomialPointGridBlock.append_state_zero,RM0256Join1_0.state_start]
theorem matrix_start : certificate.matrix 0=RM0256B00Nodes.operator 0 := by
  rw [certificate,PolynomialPointGridBlock.append_matrix_zero,RM0256Join1_0.matrix_start]
theorem state_last : certificate.state 64=RM0288B03Nodes.state 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).state (32+32)=_
  rw [PolynomialPointGridBlock.append_state_last,RM0288Join1_0.state_last]
theorem matrix_last : certificate.matrix 64=RM0288B03Nodes.operator 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).matrix (32+32)=_
  rw [PolynomialPointGridBlock.append_matrix_last,RM0288Join1_0.matrix_last]
attribute [irreducible] certificate

end
end SolitonClassification.Rotating.FullGridMJoin0_4

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
  logInfo m!"GridAssembly_FullGridMJoin0_4: {count} declarations; standard axioms only."
