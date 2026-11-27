import SolitonClassification.Rotating.IntegerShootingRoot

/-! Assemble all five derivative columns, including the variable endpoint time,
from separate enclosures on the two arms of the winding-one orbit. -/
namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

abbrev RealMatrix := Fin 5 → Fin 5 → ℝ
def realOperator (M : RealMatrix) : Parameters →L[ℝ] Parameters :=
  ContinuousLinearMap.pi fun i => ∑ j : Fin 5, M i j • ContinuousLinearMap.proj j

theorem realOperator_apply (M : RealMatrix) (x : Parameters) (i : Fin 5) :
    realOperator M x i=∑j : Fin 5,M i j*x j := by simp [realOperator]

theorem row_entry_error (M : RealMatrix) (V : ParameterMatrix) {e : ℝ} (he : 0≤e)
    (hm : ∀i j, |(V i j:ℝ)-M i j|≤e) :
    ‖parameterMatrixOperator V-realOperator M‖≤5*e := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  change |parameterMatrixOperator V x i-realOperator M x i| ≤ _
  rw [parameterMatrixOperator_apply,realOperator_apply,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑j : Fin 5, |(V i j:ℝ)*x j-M i j*x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑_j : Fin 5, e*‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [←sub_mul,abs_mul]
      exact mul_le_mul (hm i j) (norm_le_pi_norm x j) (abs_nonneg _) he
    _ = _ := by simp; ring

def assembledMatrix (xp xm : State) (cp cm : RealMatrix) (i : Fin 5) : Fin 5 → ℝ :=
  let v := fun j => cp j i-cm j i
  let k := physicalIndex i
  fun j => (physicalWeight i:ℝ) *
    (![v 0,v 2,field xp k+field xm k,
       v 1*phase 0/8+v 3*phase 1,v 4] : Fin 5 → ℝ) j

theorem rational_field (z : Fin 6 → ℚ) :
    realState (endpointField z) = field (realState z) := by
  ext i
  fin_cases i <;> simp [realState,endpointField,field]

theorem projected_derivative_enclosure (xp xm : State) (cp cm : RealMatrix)
    (hfp : ∀ i, |field (realState plusQ) i-field xp i| ≤ 1/(10:ℝ)^10)
    (hfm : ∀ i, |field (realState minusQ) i-field xm i| ≤ 1/(10:ℝ)^10)
    (hp : ∀ j i, |(plusColumn j i:ℝ)-cp j i| ≤ 1/(10:ℝ)^11)
    (hm : ∀ j i, |(minusColumn j i:ℝ)-cm j i| ≤ 1/(10:ℝ)^11) :
    ‖parameterMatrixOperator jacobianQ-realOperator (assembledMatrix xp xm cp cm)‖≤
      1/(10:ℝ)^8 := by
  apply (row_entry_error _ _ (e:=2/(10:ℝ)^9) (by positivity) _).trans (by norm_num)
  intro i j
  have weight : |(physicalWeight i:ℝ)|≤8 := by
    fin_cases i <;> norm_num [physicalWeight]
  have ep : |phase 0|≤1/8*8 := by norm_num [phase,phaseQ]
  have em : |phase 1|≤1 := by norm_num [phase,phaseQ]
  have jump (n : Fin 5) :
      |((plusColumn n i:ℝ)-(minusColumn n i:ℝ))-(cp n i-cm n i)| ≤ 2/(10:ℝ)^11 := by
    rw [show (plusColumn n i:ℝ)-(minusColumn n i:ℝ)-(cp n i-cm n i)=
        ((plusColumn n i:ℝ)-cp n i)-((minusColumn n i:ℝ)-cm n i) by ring]
    exact (abs_sub _ _).trans (by linarith [hp n i,hm n i])
  have vf (k : Fin 6) : |((endpointField plusQ k:ℝ)+(endpointField minusQ k:ℝ))-
      (field xp k+field xm k)| ≤ 2/(10:ℝ)^10 := by
    change |(realState (endpointField plusQ) k+realState (endpointField minusQ) k)-_| ≤ _
    rw [rational_field,rational_field,show field (realState plusQ) k+field (realState minusQ) k-
      (field xp k+field xm k)=(field (realState plusQ) k-field xp k)+
      (field (realState minusQ) k-field xm k) by ring]
    exact (abs_add_le _ _).trans (by linarith [hfp k,hfm k])
  have ph :
      |(((plusColumn 1 i:ℝ)-(minusColumn 1 i:ℝ))*phase 0/8+
         ((plusColumn 3 i:ℝ)-(minusColumn 3 i:ℝ))*phase 1)-
        ((cp 1 i-cm 1 i)*phase 0/8+(cp 3 i-cm 3 i)*phase 1)| ≤ 2/(10:ℝ)^10 := by
    rw [show _-((cp 1 i-cm 1 i)*phase 0/8+(cp 3 i-cm 3 i)*phase 1)=
      (((plusColumn 1 i:ℝ)-(minusColumn 1 i:ℝ))-(cp 1 i-cm 1 i))*phase 0/8+
      (((plusColumn 3 i:ℝ)-(minusColumn 3 i:ℝ))-(cp 3 i-cm 3 i))*phase 1 by ring]
    apply (abs_add_le _ _).trans
    rw [abs_div,abs_mul,abs_mul]
    have h1 := mul_le_mul (jump 1) ep (abs_nonneg _) (by positivity)
    have h3 := mul_le_mul (jump 3) em (abs_nonneg _) (by positivity)
    norm_num at h1 h3 ⊢
    linarith
  have scaled (x y : ℝ) (hxy : |x-y|≤2/(10:ℝ)^10) :
      |(physicalWeight i:ℝ)*x-(physicalWeight i:ℝ)*y|≤2/(10:ℝ)^9 := by
    rw [←mul_sub,abs_mul]
    exact (mul_le_mul weight hxy (abs_nonneg _) (by norm_num)).trans (by norm_num)
  fin_cases j <;> simp only [jacobianQ,assembledMatrix,Rat.cast_mul] <;> apply scaled
  · change |((plusColumn 0 i-minusColumn 0 i : ℚ):ℝ)-(cp 0 i-cm 0 i)|≤_
    push_cast
    exact (jump 0).trans (by norm_num)
  · change |((plusColumn 2 i-minusColumn 2 i : ℚ):ℝ)-(cp 2 i-cm 2 i)|≤_
    push_cast
    exact (jump 2).trans (by norm_num)
  · change |((endpointField plusQ _+endpointField minusQ _ : ℚ):ℝ)-
      (field xp _+field xm _)|≤_
    push_cast
    exact vf _
  · change |((((plusColumn 1 i-minusColumn 1 i)*phaseQ 0/8+
      (plusColumn 3 i-minusColumn 3 i)*phaseQ 1):ℚ):ℝ)-
      ((cp 1 i-cm 1 i)*phase 0/8+(cp 3 i-cm 3 i)*phase 1)|≤_
    push_cast
    exact ph
  · change |((plusColumn 4 i-minusColumn 4 i : ℚ):ℝ)-(cp 4 i-cm 4 i)|≤_
    push_cast
    exact (jump 4).trans (by norm_num)

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.projected_derivative_enclosure
