import SolitonClassification.Rotating.IntegerPhysicalFromRows
import SolitonClassification.Rotating.ResetCompleteMinus

namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
open DyadicReset
set_option maxHeartbeats 1500000

/-- State, parameter differential and moving-endpoint bounds for the complete
negative arm of the actual shooting equation. -/
theorem actual_backward_shooting :
    ArmBounds wideFlow selectedDerivative (backwardEndpointInput phase) minusQ minusColumn := by
  let M := CompleteMinus.tape
  have start : M.node 0=initialNode :=
    (CompleteMinus.range 0 (by decide)).1.trans actual_grid_ends.2.1
  have finish (j : ℕ) : (M.data 3999 j).sum=(minusNode[j]?).getD 0 := by
    change (packedData (CompleteMinus.atRow 3999).input j).sum=_
    rw [packed_sum,(CompleteMinus.atRow 3999).endpoints.2,(CompleteMinus.range 3999 (by decide)).2,
      actual_grid_ends.2.2.2]
  have neg := minus_numbers M start finish
  apply arm_from_tape M neg (backwardEndpointInput phase) (fun _ => rfl) minus_half_step
  intro c hc
  change |-(c 2)-(-(center 2))|≤1/10^30
  rw [show -(c 2)-(-(center 2))= -(c 2-center 2) by ring,abs_neg]
  exact (norm_le_pi_norm (c-center) 2).trans (show ‖c-center‖≤1/(10:ℝ)^30 from hc)

theorem physical_evolution_from_positive_rows
    (p : ℕ → TapeRow Middle.hn)
    (hp : ∀i : ℕ, i<4000 → (p i).left=GridPlus.atNode i ∧ (p i).right=GridPlus.atNode (i+1)) :
    ∃P : Physical.Seed, Physical.PrimitiveEvolution P :=
  Physical.physical_evolution_of_indexed_rows p CompleteMinus.atRow hp CompleteMinus.range

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.actual_backward_shooting
#print axioms SolitonClassification.Rotating.IntegerTarget.physical_evolution_from_positive_rows
