import SolitonClassification.Rotating.ShootingRoot

/-! Five-dimensional rational matrices and the actual supremum operator
norm used by the shooting problem. Row and column indices are explicit. -/
namespace SolitonClassification.Rotating
noncomputable section
open Finset
set_option Elab.async false

abbrev ParameterMatrix := Fin 5 → Fin 5 → ℚ

def parameterMatrixOperator (M : ParameterMatrix) : Parameters →L[ℝ] Parameters :=
  ContinuousLinearMap.pi fun i => ∑j : Fin 5,(M i j:ℝ) • ContinuousLinearMap.proj j

theorem parameterMatrixOperator_apply (M : ParameterMatrix) (x : Parameters) (i : Fin 5) :
    parameterMatrixOperator M x i=∑j : Fin 5,(M i j:ℝ)*x j := by
  simp [parameterMatrixOperator]

def parameterMatrixMul (M N : ParameterMatrix) : ParameterMatrix :=
  fun i j => ∑k : Fin 5,M i k*N k j

def parameterMatrixId : ParameterMatrix := fun i j => if i=j then 1 else 0

theorem parameterMatrixOperator_identity :
    parameterMatrixOperator parameterMatrixId=ContinuousLinearMap.id ℝ Parameters := by
  ext x i
  simp [parameterMatrixOperator_apply,parameterMatrixId,apply_ite]

theorem parameterMatrixOperator_sub (M N : ParameterMatrix) :
    parameterMatrixOperator (M-N)=parameterMatrixOperator M-parameterMatrixOperator N := by
  ext x i
  simp [parameterMatrixOperator_apply,Finset.sum_sub_distrib,sub_mul]

theorem parameterMatrixOperator_comp (M N : ParameterMatrix) :
    (parameterMatrixOperator M).comp (parameterMatrixOperator N)=
      parameterMatrixOperator (parameterMatrixMul M N) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply,parameterMatrixOperator_apply,parameterMatrixMul,
    Rat.cast_sum,Rat.cast_mul,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem parameterMatrixOperator_norm_le (M : ParameterMatrix) {C : ℚ} (hC : 0≤C)
    (hrow : ∀i : Fin 5,∑j : Fin 5,|M i j|≤C) :
    ‖parameterMatrixOperator M‖≤(C:ℝ) := by
  have hCr : (0:ℝ)≤(C:ℝ) := by exact_mod_cast hC
  apply ContinuousLinearMap.opNorm_le_bound _ hCr
  intro x
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hCr (norm_nonneg x))]
  intro i
  have hrowr : (∑j : Fin 5,|(M i j:ℝ)|)≤(C:ℝ) := by exact_mod_cast hrow i
  rw [Real.norm_eq_abs,parameterMatrixOperator_apply]
  calc
    _ ≤ ∑j : Fin 5,|(M i j:ℝ)*x j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑j : Fin 5,|(M i j:ℝ)| * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
    _ = (∑j : Fin 5,|(M i j:ℝ)|)*‖x‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ (C:ℝ)*‖x‖ := mul_le_mul_of_nonneg_right hrowr (norm_nonneg x)

theorem parameterMatrixOperator_defect_norm (B J : ParameterMatrix) {q : ℚ}
    (hq : 0≤q)
    (hrow : ∀i : Fin 5,∑j : Fin 5,|parameterMatrixId i j-parameterMatrixMul B J i j|≤q) :
    ‖ContinuousLinearMap.id ℝ Parameters-
      (parameterMatrixOperator B).comp (parameterMatrixOperator J)‖≤(q:ℝ) := by
  rw [parameterMatrixOperator_comp,←parameterMatrixOperator_identity,←parameterMatrixOperator_sub]
  exact parameterMatrixOperator_norm_le _ hq hrow

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.parameterMatrixOperator_defect_norm
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Actual parameter matrix operator audit passed: {count} declarations; standard axioms only."
