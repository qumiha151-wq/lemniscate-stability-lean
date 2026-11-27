import SolitonClassification.Rotating.IntegerShootingData

/-! Exact integer-angle closure from uniform state and derivative enclosures.
The finite matrix and the irrational target are checked here. The two true
endpoint estimates and the uniform true derivative estimate are hypotheses. -/
namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
open Metric Set
open scoped NNReal
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

def center : Parameters := fun i => (centerQ i:ℝ)
def phase : Fin 2 → ℝ := fun i => (phaseQ i:ℝ)
def realState (z : Fin 6 → ℚ) : State := fun i => (z i:ℝ)
def angle (a : ℝ) : Parameters := ![0,0,0,0,a]
def residual (Φ : ℝ×State → State) (c : Parameters) : Parameters :=
  shootingProjection (Φ (forwardEndpointInput phase c)-Φ (backwardEndpointInput phase c))+
    angle (2*Real.pi)

theorem proxy_identity :
    (fun i => (residualQ i:ℝ) : Parameters) =
    shootingProjection (realState plusQ-realState minusQ)+angle (2*(piFloor:ℝ)) := by
  rw [shootingProjection_apply]
  ext i
  fin_cases i <;> simp [residualQ,physicalIndex,physicalWeight,angle,realState]

theorem angle_error : ‖angle (2*Real.pi)-angle (2*(piFloor:ℝ))‖ ≤ 2/(10:ℝ)^56 := by
  have hl := pi_lower
  have hu := pi_upper
  push_cast at hu
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i <;> simp [angle,Real.norm_eq_abs] <;> try positivity
  rw [abs_of_nonneg (by linarith)]
  linarith

theorem center_residual (Φ : ℝ×State → State)
    (hp : ‖Φ (forwardEndpointInput phase center)-realState plusQ‖ ≤ 1/(10:ℝ)^50)
    (hm : ‖Φ (backwardEndpointInput phase center)-realState minusQ‖ ≤ 1/(10:ℝ)^50) :
    ‖residual Φ center‖ ≤ 2/(10:ℝ)^40 := by
  let a := Φ (forwardEndpointInput phase center)-realState plusQ
  let b := Φ (backwardEndpointInput phase center)-realState minusQ
  have hab : ‖a-b‖ ≤ 2/(10:ℝ)^50 := by
    have hn := norm_sub_le a b
    change ‖a‖ ≤ _ at hp
    change ‖b‖ ≤ _ at hm
    linarith
  have herr : ‖shootingProjection (a-b)‖ ≤ 8*(2/(10:ℝ)^50) :=
    (shootingProjection.le_opNorm _).trans
      (mul_le_mul shootingProjection_norm hab (norm_nonneg _) (by norm_num))
  have he : residual Φ center = (fun i => (residualQ i:ℝ) : Parameters)+
      shootingProjection (a-b)+(angle (2*Real.pi)-angle (2*(piFloor:ℝ))) := by
    rw [proxy_identity]
    simp only [residual,a,b,map_sub]
    abel
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add residual_bound herr)) angle_error)).trans (by norm_num)

theorem residual_deriv (Φ : ℝ×State → State) (DΦ : ℝ×State → (ℝ×State) →L[ℝ] State)
    (c : Parameters)
    (hp : HasFDerivAt Φ (DΦ (forwardEndpointInput phase c)) (forwardEndpointInput phase c))
    (hm : HasFDerivAt Φ (DΦ (backwardEndpointInput phase c)) (backwardEndpointInput phase c)) :
    HasFDerivAt (residual Φ) (shootingDerivative phase DΦ c) c :=
  (shootingProjection.hasFDerivAt.comp c
    ((hp.comp c (forwardEndpointInput phase).hasFDerivAt).sub
      (hm.comp c (backwardEndpointInput phase).hasFDerivAt))).add_const _

theorem unique_root_of_endpoint_bounds
    (Φ : ℝ×State → State) (DΦ : ℝ×State → (ℝ×State) →L[ℝ] State)
    (hstateP : ‖Φ (forwardEndpointInput phase center)-realState plusQ‖ ≤ 1/(10:ℝ)^50)
    (hstateM : ‖Φ (backwardEndpointInput phase center)-realState minusQ‖ ≤ 1/(10:ℝ)^50)
    (hflowP : ∀ c ∈ closedBall center (1/(10:ℝ)^30),
      HasFDerivAt Φ (DΦ (forwardEndpointInput phase c)) (forwardEndpointInput phase c))
    (hflowM : ∀ c ∈ closedBall center (1/(10:ℝ)^30),
      HasFDerivAt Φ (DΦ (backwardEndpointInput phase c)) (backwardEndpointInput phase c))
    (hder : ∀ c ∈ closedBall center (1/(10:ℝ)^30),
      ‖parameterMatrixOperator jacobianQ-shootingDerivative phase DΦ c‖ ≤ 1/(10:ℝ)^8) :
    ∃ c ∈ closedBall center (1/(10:ℝ)^30), residual Φ c=0 ∧
      ∀ c' ∈ closedBall center (1/(10:ℝ)^30), residual Φ c'=0 → c'=c := by
  let B := parameterMatrixOperator inverseQ
  let J := parameterMatrixOperator jacobianQ
  have hinj : Function.Injective B :=
    preconditioner_injective_of_defect B J (defect_bound.trans_lt (by norm_num))
  apply exists_unique_zero_of_preconditioned_bounds (residual Φ) (shootingDerivative phase DΦ)
    B center (1/(10:ℝ)^30) (26/(10:ℝ)^40) (1/2) (by positivity) (by norm_num) hinj
  · intro c hc
    exact residual_deriv Φ DΦ c (hflowP c hc) (hflowM c hc)
  · intro c hc
    let D := shootingDerivative phase DΦ c
    have he : ContinuousLinearMap.id ℝ Parameters-B.comp D =
        (ContinuousLinearMap.id ℝ Parameters-B.comp J)+B.comp (J-D) := by
      ext v i
      simp only [sub_apply,add_apply,ContinuousLinearMap.comp_apply,map_sub,Pi.sub_apply,
        Pi.add_apply]
      abel
    change ‖ContinuousLinearMap.id ℝ Parameters-B.comp D‖ ≤ _
    rw [he]
    have hn := (norm_add_le _ _).trans (add_le_add defect_bound
      ((B.opNorm_comp_le (J-D)).trans (mul_le_mul inverse_bound (hder c hc)
        (norm_nonneg _) (by norm_num))))
    exact hn.trans (by norm_num)
  · exact ((B.le_opNorm _).trans (mul_le_mul inverse_bound
      (center_residual Φ hstateP hstateM) (norm_nonneg _) (by norm_num))).trans (by norm_num)
  · norm_num

theorem residual_zero_iff (Φ : ℝ×State → State) (c : Parameters) :
    residual Φ c=0 ↔
    Φ (forwardEndpointInput phase c) 0=Φ (backwardEndpointInput phase c) 0 ∧
    Φ (forwardEndpointInput phase c) 1=Φ (backwardEndpointInput phase c) 1 ∧
    Φ (forwardEndpointInput phase c) 2=Φ (backwardEndpointInput phase c) 2 ∧
    Φ (forwardEndpointInput phase c) 3=Φ (backwardEndpointInput phase c) 3 ∧
    Φ (forwardEndpointInput phase c) 5-Φ (backwardEndpointInput phase c) 5= -2*Real.pi := by
  constructor
  · intro h
    have hh (i : Fin 5) := congrFun h i
    have h0 := hh 0
    have h1 := hh 1
    have h2 := hh 2
    have h3 := hh 3
    have h4 := hh 4
    simp [residual,shootingProjection,angle] at h0 h1 h2 h3 h4
    exact ⟨sub_eq_zero.mp h0,by linarith,sub_eq_zero.mp h2,sub_eq_zero.mp h3,by linarith⟩
  · rintro ⟨h0,h1,h2,h3,h4⟩
    ext i
    fin_cases i <;> simp [residual,shootingProjection,angle,h0,h1,h2,h3,h4]

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.unique_root_of_endpoint_bounds
