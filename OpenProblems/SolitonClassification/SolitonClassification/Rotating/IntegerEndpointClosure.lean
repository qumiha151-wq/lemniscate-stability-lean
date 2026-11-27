import SolitonClassification.Rotating.IntegerPhysicalColumns
import SolitonClassification.Rotating.ResetAugmentedBounds

namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
open Metric Set
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

private theorem field_error {q : Fin 6 → ℚ} {x : State}
    (hq : ∀i, |q i|≤8) (hx : ‖x-realState q‖≤1/(10:ℝ)^12) (i : Fin 6) :
    |field (realState q) i-field x i|≤1/(10:ℝ)^10 := by
  let a : DyadicReset.Aug := (realState q,0)
  let b : DyadicReset.Aug := (x,0)
  have aq (j : Fin 6) : |realState q j|≤8 := by
    simpa only [realState,Rat.cast_abs,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr (hq j)
  have ha : DyadicReset.Box a := ⟨fun j _ => (aq j).trans (by norm_num),by simp [a]⟩
  have hb : DyadicReset.Box b := by
    refine ⟨?_,by simp [b]⟩
    intro j _
    have d := coordinate_bound (x-realState q) j
    change |x j-realState q j|≤_ at d
    have tri := abs_add_le (x j-realState q j) (realState q j)
    rw [sub_add_cancel] at tri
    change |x j|≤10
    linarith [aq j]
  have lip := DyadicReset.augmented_lipschitz a b ha hb
  have hnorm : ‖a-b‖=‖x-realState q‖ := by simp [a,b,Prod.norm_def,norm_sub_rev]
  rw [hnorm] at lip
  have coord := DyadicReset.state_diff (DyadicReset.augmented a) (DyadicReset.augmented b) i
  change |field (realState q) i-field x i|≤_ at coord
  linarith

def cube := closedBall center (1/(10:ℝ)^30)

/-- A quantitative statement on both arms. The variational errors compare
actual initial-value derivatives on the cube with the rational tape columns. -/
structure ArmBounds (Φ : ℝ×State → State) (DΦ : ℝ×State → (ℝ×State) →L[ℝ] State)
    (input : Parameters →L[ℝ] (ℝ×State)) (q : Fin 6 → ℚ) (cols : ParameterMatrix) : Prop where
  centerState : ‖Φ (input center)-realState q‖≤1/(10:ℝ)^50
  cubeState : ∀c∈cube, ‖Φ (input c)-realState q‖≤1/(10:ℝ)^12
  differentiable : ∀c∈cube, HasFDerivAt Φ (DΦ (input c)) (input c)
  timeColumn : ∀c∈cube, DΦ (input c) (1,0)=field (Φ (input c))
  stateColumns : ∀c∈cube, ∀j i, |(cols j i:ℝ)-jointColumns (DΦ (input c)) j i|≤1/(10:ℝ)^11

theorem unique_root_of_arm_bounds (Φ : ℝ×State → State) (DΦ : ℝ×State → (ℝ×State) →L[ℝ] State)
    (hp : ArmBounds Φ DΦ (forwardEndpointInput phase) plusQ plusColumn)
    (hm : ArmBounds Φ DΦ (backwardEndpointInput phase) minusQ minusColumn) :
    ∃ c ∈ cube, residual Φ c=0 ∧ ∀c'∈cube, residual Φ c'=0 → c'=c := by
  apply unique_root_of_endpoint_bounds Φ DΦ hp.centerState hm.centerState hp.differentiable hm.differentiable
  intro c hc
  rw [physical_assembly DΦ c _ _ (hp.timeColumn c hc) (hm.timeColumn c hc)]
  exact projected_derivative_enclosure _ _ _ _
    (field_error (by decide +kernel) (hp.cubeState c hc))
    (field_error (by decide +kernel) (hm.cubeState c hc))
    (hp.stateColumns c hc) (hm.stateColumns c hc)

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.unique_root_of_arm_bounds
