module

public import SolitonClassification.Rotating.FlowBootstrapCoordinates
public import SolitonClassification.Rotating.FlowMetricReset

@[expose] public section

/-! State-coordinate reset with both matrix and reference-state jumps.
The physical actual state is the same on both sides of a reset. -/
namespace SolitonClassification.Rotating
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem bootstrap_reset_identity (x a b : State) (M N : FlowEnd) (hM : IsUnit M) :
    Ring.inverse N (x-b)=(Ring.inverse N*M) (Ring.inverse M (x-a))+Ring.inverse N (a-b) := by
  have he : M (Ring.inverse M (x-a))=x-a :=
    congrArg (fun L : FlowEnd => L (x-a)) (Ring.mul_inverse_cancel M hM)
  change Ring.inverse N (x-b)=Ring.inverse N (M (Ring.inverse M (x-a)))+Ring.inverse N (a-b)
  rw [he,←map_add]
  congr 1
  abel

theorem bootstrap_reset_bound {x a b : State} {M N : FlowEnd} {I δM δX : ℝ}
    (hM : IsUnit M) (hN : IsUnit N) (hI : 0≤I)
    (hInv : ‖Ring.inverse N‖≤I) (hMatrix : ‖M-N‖≤δM) (hState : ‖a-b‖≤δX) :
    ‖Ring.inverse N (x-b)‖≤(1+I*δM)*‖Ring.inverse M (x-a)‖+I*δX := by
  rw [bootstrap_reset_identity x a b M N hM]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact ((Ring.inverse N*M).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (metric_transition_norm_bound hN hI hInv hMatrix) (norm_nonneg _))
  · exact ((Ring.inverse N).le_opNorm _).trans (mul_le_mul hInv hState (norm_nonneg _) hI)

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating nonlinear state reset audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating nonlinear state reset audit passed for {count} declarations."

end
