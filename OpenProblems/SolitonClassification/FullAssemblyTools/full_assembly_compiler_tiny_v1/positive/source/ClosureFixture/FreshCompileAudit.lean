module
public import ClosureFixture.D

@[expose] public section
namespace ClosureFixture.FreshCompileAudit
noncomputable section
set_option Elab.async false
theorem result : ClosureFixture.c = 9 := ClosureFixture.result
end
end ClosureFixture.FreshCompileAudit

#check ClosureFixture.a_eq
#print axioms ClosureFixture.a_eq
#check ClosureFixture.b_eq
#print axioms ClosureFixture.b_eq
#check ClosureFixture.c_eq
#print axioms ClosureFixture.c_eq
#check ClosureFixture.result
#print axioms ClosureFixture.result
#check ClosureFixture.FreshCompileAudit.result
#print axioms ClosureFixture.FreshCompileAudit.result
open Lean Elab Command in
run_cmd do
  let info ← getConstInfo `ClosureFixture.FreshCompileAudit.result
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
  logInfo m!"TINY_SEQUENCE_ACTUAL_STANDARD3 {count}"
