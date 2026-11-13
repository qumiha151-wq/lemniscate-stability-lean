module

public import SolitonClassification.Rotating.MatrixColumnNorm
public import SolitonClassification.Rotating.RationalBall

@[expose] public section

/-! Exact row-sum checks for rational reference matrices. This is the
supremum operator norm on the full six-dimensional state. -/
namespace SolitonClassification.Rotating
noncomputable section
open Finset
set_option Elab.async false

theorem operator_norm_le_row_sum (A : State →L[ℝ] State) {C : ℝ} (hC : 0≤C)
    (h : ∀i : Fin 6,∑j : Fin 6,|A (coordinateBasis j) i|≤C) : ‖A‖≤C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg v))]
  intro i
  have he : A v i=∑j : Fin 6,v j*A (coordinateBasis j) i := by
    conv_lhs => rw [state_basis_expansion v]
    simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [Real.norm_eq_abs,he]
  calc
    _ ≤ ∑j : Fin 6,|v j*A (coordinateBasis j) i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑j : Fin 6,‖v‖*|A (coordinateBasis j) i| := by
      apply sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (coordinate_bound v j) (abs_nonneg _)
    _ = ‖v‖*(∑j : Fin 6,|A (coordinateBasis j) i|) := (mul_sum _ _ _).symm
    _ ≤ ‖v‖*C := mul_le_mul_of_nonneg_left (h i) (norm_nonneg v)
    _ = C*‖v‖ := mul_comm _ _

def rationalColumnOperator (W : Fin 6 → Fin 6 → ℚ) : State →L[ℝ] State :=
  columnOperator (fun j i=>(W j i:ℝ))

theorem rationalColumnOperator_norm_le (W : Fin 6 → Fin 6 → ℚ) {C : ℚ} (hC : 0≤C)
    (h : ∀i : Fin 6,∑j : Fin 6,|W j i|≤C) : ‖rationalColumnOperator W‖≤(C:ℝ) := by
  apply operator_norm_le_row_sum _ (by exact_mod_cast hC)
  intro i
  simp only [rationalColumnOperator,columnOperator_basis]
  exact_mod_cast h i

theorem rationalColumnOperator_sub_one_norm_le (W : Fin 6 → Fin 6 → ℚ) {C : ℚ} (hC : 0≤C)
    (h : ∀i : Fin 6,∑j : Fin 6,|W j i-(if i=j then 1 else 0)|≤C) :
    ‖rationalColumnOperator W-1‖≤(C:ℝ) := by
  apply operator_norm_le_row_sum _ (by exact_mod_cast hC)
  intro i
  have hh : (∑j : Fin 6,|(W j i:ℝ)-((if i=j then 1 else 0:ℚ):ℝ)|)≤(C:ℝ) := by
    exact_mod_cast h i
  have hc (j : Fin 6) : ((if i=j then 1 else 0:ℚ):ℝ)=(if i=j then 1 else 0:ℝ) := by
    by_cases hij : i=j <;> simp [hij]
  simp only [hc] at hh
  simpa [rationalColumnOperator,columnOperator_basis,coordinateBasis] using hh

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.rationalColumnOperator_sub_one_norm_le
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Full rational row-sum operator norm audit passed."

end
