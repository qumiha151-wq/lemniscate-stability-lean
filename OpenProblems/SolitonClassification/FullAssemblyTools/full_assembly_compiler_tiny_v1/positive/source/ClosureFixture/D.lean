module
public import ClosureFixture.C
public import Lean

@[expose] public section
namespace ClosureFixture
theorem result : c = 9 := c_eq
end ClosureFixture
#print axioms ClosureFixture.result
open Lean Elab Command in
run_cmd do
  unless (← collectAxioms `ClosureFixture.result).isEmpty do throwError "Unexpected fixture axiom"
  logInfo "FOUR_MODULE_RECURSIVE_PUBLIC_CLOSURE_CHECKED"
