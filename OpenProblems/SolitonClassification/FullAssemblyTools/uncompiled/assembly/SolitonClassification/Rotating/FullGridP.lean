module
public import SolitonClassification.Rotating.FullGridPJoin6_0

@[expose] public section

namespace SolitonClassification.Rotating.FullGridP
open Candidate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

def certificate : PolynomialPointGridBlock (1:ℝ) (step:ℝ) (1/10^55) (1/10^55) 4000 :=
  FullGridPJoin6_0.certificate
theorem state_start : certificate.state 0=initial := by
  rw [certificate,FullGridPJoin6_0.state_start,RP0000B00Nodes.state_initial]
theorem matrix_start : certificate.matrix 0=1 := by
  rw [certificate,FullGridPJoin6_0.matrix_start,RP0000B00Nodes.operator_initial]
theorem state_last : certificate.state 4000=RP3968B03Nodes.state 8 := FullGridPJoin6_0.state_last
theorem matrix_last : certificate.matrix 4000=RP3968B03Nodes.operator 8 := FullGridPJoin6_0.matrix_last
attribute [irreducible] certificate

end
end SolitonClassification.Rotating.FullGridP

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
  logInfo m!"GridAssembly_FullGridP: {count} declarations; standard axioms only."
