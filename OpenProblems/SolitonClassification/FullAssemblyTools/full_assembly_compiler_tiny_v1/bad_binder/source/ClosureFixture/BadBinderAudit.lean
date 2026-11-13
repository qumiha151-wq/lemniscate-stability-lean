module
public import ClosureFixture.D

@[expose] public section
namespace ClosureFixture.BadBinderAudit
noncomputable section
set_option Elab.async false
theorem result : (n : Nat) → n = n := fun _ => rfl
end
end ClosureFixture.BadBinderAudit


#check ClosureFixture.BadBinderAudit.result
#print axioms ClosureFixture.BadBinderAudit.result
open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `ClosureFixture.BadBinderAudit.result
  if info.type.isForall then throwError "Final alias has an additional binder"
  unless info.levelParams.isEmpty do throwError "Final alias has universe parameters"
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    let userName := privateToUserName name
    if (`ClosureFixture).isPrefixOf userName then
      for ax in (← collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Unexpected axiom: {name} depends on {ax}"
      count := count + 1
  logInfo m!"BAD_BINDER_MUST_NOT_PASS {count}"
