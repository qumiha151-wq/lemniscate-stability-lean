import SolitonClassification.Rotating.CandidateInitial
import SolitonClassification.Rotating.FixedTaylor

/-! Kernel re-execution of this candidate's actual order-60 polynomial.
This is not an ODE endpoint or periodic root certificate. -/
namespace SolitonClassification.Rotating.Candidate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def recordedFirstPolynomial : Vector FixedBall 6 := Vector.ofFn ![⟨7494485587272866628371857589672382194505315471430276251128452,4⟩,⟨-207182152848262066989235424010915645287329506060227571634505,29⟩,⟨1541393746582515986543723412085832346604076617531334330820595,3⟩,⟨97449163322859813102172709364481205298057334383097687940202,15⟩,⟨9686618454842835404334516933620537128639073700599650566920,3⟩,⟨58520760540799353622131175627837544692123532551436715475968,10⟩]

theorem first_polynomial60_computed :
    fixedTaylorEndpoint mesh step initialBalls 60=recordedFirstPolynomial := by
  decide +kernel

theorem first_polynomial60_enclosed (i : Fin 6) :
    (recordedFirstPolynomial[i.val]).Contains mesh
      ((taylorPolynomial initial 60 i).eval (step:ℝ)) := by
  rw [←first_polynomial60_computed]
  exact fixedTaylorEndpoint_contains mesh_pos step initial_enclosed 60 i

end SolitonClassification.Rotating.Candidate

#print axioms SolitonClassification.Rotating.Candidate.first_polynomial60_enclosed

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
  logInfo "Rotating actual order-60 polynomial audit passed; standard axioms only."
