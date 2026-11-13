module
public import SolitonClassification.Rotating.FullGridP
public import SolitonClassification.Rotating.FullGridM

@[expose] public section

namespace SolitonClassification.Rotating.FullGridAssemblyAudit
open Candidate
noncomputable section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

#print axioms SolitonClassification.Rotating.FullGridP.certificate
#print axioms SolitonClassification.Rotating.FullGridM.certificate

end
end SolitonClassification.Rotating.FullGridAssemblyAudit

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
  logInfo m!"GridAssembly_FullGridAssemblyAudit: {count} declarations; standard axioms only."
