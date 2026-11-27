import SolitonClassification.Rotating.IntegerDerivativeAssembly
namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
open Metric Set
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def basisVector {n : ℕ} (j : Fin n) : Fin n → ℝ := fun k => if j=k then 1 else 0

def stateInput (j : Fin 5) : ℝ×State := (0,basisVector j.castSucc)

def jointColumns (A : ℝ×State →L[ℝ] State) : RealMatrix :=
  fun j i => A (stateInput j) (physicalIndex i)

theorem shootingProjection_coordinate (y : State) (i : Fin 5) :
    shootingProjection y i = (physicalWeight i:ℝ)* y (physicalIndex i) := by
  rw [shootingProjection_apply]
  fin_cases i <;> simp [physicalWeight,physicalIndex]

private theorem basis_decomposition (x : Parameters) : ∑j : Fin 5,x j • basisVector j=x := by
  ext i
  simp [Finset.sum_apply,Pi.smul_apply,basisVector,smul_eq_mul,mul_ite]

private theorem operator_on_basis (M : RealMatrix) (j i : Fin 5) :
    realOperator M (basisVector j) i=M i j := by
  simp [realOperator_apply,basisVector,mul_ite]

private theorem endpoints_on_basis (u : Parameters →L[ℝ] (ℝ×State))
    (s : ℝ) (h : ∀x, u x=(s*x 2,shootingInitial phase x)) (j : Fin 5) :
    u (basisVector j) =
      (![stateInput 0,stateInput 2,(s,0),
        (phase 0/8) • stateInput 1+phase 1 • stateInput 3,stateInput 4] : Fin 5 → ℝ×State) j := by
  rw [h,shootingInitial_apply]
  apply Prod.ext
  · fin_cases j <;> simp (config := {decide := true}) [stateInput,basisVector]
  · ext i
    fin_cases j <;> fin_cases i <;> simp (config := {decide := true}) [stateInput,basisVector]

theorem physical_assembly (DΦ : ℝ×State → (ℝ×State) →L[ℝ] State) (c : Parameters)
    (xp xm : State)
    (hp : DΦ (forwardEndpointInput phase c) (1,0)=field xp)
    (hm : DΦ (backwardEndpointInput phase c) (1,0)=field xm) :
    shootingDerivative phase DΦ c =
      realOperator (assembledMatrix xp xm (jointColumns (DΦ (forwardEndpointInput phase c)))
        (jointColumns (DΦ (backwardEndpointInput phase c)))) := by
  let P := DΦ (forwardEndpointInput phase c)
  let M := DΦ (backwardEndpointInput phase c)
  let A := shootingDerivative phase DΦ c
  let B := realOperator (assembledMatrix xp xm (jointColumns P) (jointColumns M))
  have hn : M ((-1:ℝ),(0:State))= -(field xm) := by
    rw [show ((-1:ℝ),(0:State))= -((1:ℝ),(0:State)) by simp,map_neg,←hm]
  have plus := endpoints_on_basis (forwardEndpointInput phase) 1 (by intro x; simp [forwardEndpointInput,shootingLength])
  have minus := endpoints_on_basis (backwardEndpointInput phase) (-1) (by intro x; simp [backwardEndpointInput,shootingLength])
  have eqv (j : Fin 5) : A (basisVector j)=B (basisVector j) := by
    ext i
    change shootingProjection (P (forwardEndpointInput phase (basisVector j))-
      M (backwardEndpointInput phase (basisVector j))) i = _
    rw [shootingProjection_coordinate,plus,minus]
    rw [show B=realOperator (assembledMatrix xp xm (jointColumns P) (jointColumns M)) by rfl,
      operator_on_basis]
    have hh : P ((1:ℝ),(0:State))=field xp := hp
    fin_cases j <;> simp [assembledMatrix,jointColumns,hh,hn,sub_eq_add_neg]
    ring_nf
    simp
  apply ContinuousLinearMap.ext
  intro x
  change A x=B x
  calc
    A x=A (∑j : Fin 5,x j • basisVector j) := congrArg A (basis_decomposition x).symm
    _ = B (∑j : Fin 5,x j • basisVector j) := by simp only [map_sum,map_smul,eqv]
    _ = B x := congrArg B (basis_decomposition x)

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.physical_assembly
