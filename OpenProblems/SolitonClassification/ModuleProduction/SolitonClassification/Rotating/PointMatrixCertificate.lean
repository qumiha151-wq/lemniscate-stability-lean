module

public import SolitonClassification.Rotating.PointMatrixInverse
public import SolitonClassification.Rotating.MatrixRowNorm

@[expose] public section

/-! Integer-only row and two-product checks for point matrices on a
shared mesh. The checker may propose an approximate inverse C; these
theorems connect its finite integer products to the actual real inverse.
Indices are column first, row second, as in the full variational tables. -/
namespace SolitonClassification.Rotating
noncomputable section
open Finset
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

abbrev PointMatrix := Fin 6 → Fin 6 → ℤ

def pointMatrixOperator (S : ℕ) (A : PointMatrix) : FlowEnd :=
  rationalColumnOperator (fun j i=>(A j i:ℚ)/S)

def pointMatrixProduct (A B : PointMatrix) (j i : Fin 6) : ℤ :=
  ∑k : Fin 6,A k i*B j k

def pointMatrixDefect (S : ℕ) (A B : PointMatrix) (j i : Fin 6) : ℤ :=
  pointMatrixProduct A B j i-(if i=j then (S:ℤ)^2 else 0)

theorem pointMatrixOperator_basis (S : ℕ) (A : PointMatrix) (j i : Fin 6) :
    pointMatrixOperator S A (coordinateBasis j) i=(A j i:ℝ)/(S:ℝ) := by
  simp only [pointMatrixOperator,rationalColumnOperator,columnOperator_basis,
    Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]

theorem pointMatrixOperator_norm {S : ℕ} (hS : 0<S) (A : PointMatrix) {K : ℤ}
    (hK : 0≤K) (hrow : ∀i,∑j : Fin 6,|A j i|≤K) :
    ‖pointMatrixOperator S A‖≤(K:ℝ)/(S:ℝ) := by
  have hs : (0:ℝ)<S := by exact_mod_cast hS
  apply operator_norm_le_row_sum _ (div_nonneg (by exact_mod_cast hK) hs.le)
  intro i
  have hr : (∑j : Fin 6,|(A j i:ℝ)|)≤(K:ℝ) := by exact_mod_cast hrow i
  simp only [pointMatrixOperator_basis,abs_div,abs_of_nonneg hs.le,←Finset.sum_div]
  exact div_le_div_of_nonneg_right hr hs.le

theorem pointMatrixOperator_product_basis {S : ℕ} (hS : 0<S)
    (A B : PointMatrix) (j i : Fin 6) :
    (pointMatrixOperator S A*pointMatrixOperator S B) (coordinateBasis j) i=
      (pointMatrixProduct A B j i:ℝ)/(S:ℝ)^2 := by
  have hs : (S:ℝ)≠0 := ne_of_gt (by exact_mod_cast hS)
  change pointMatrixOperator S A (pointMatrixOperator S B (coordinateBasis j)) i=_
  rw [show pointMatrixOperator S B (coordinateBasis j)=(fun k=>(B j k:ℝ)/(S:ℝ)) from
    funext (fun k=>pointMatrixOperator_basis S B j k)]
  simp only [pointMatrixOperator,rationalColumnOperator,columnOperator_apply,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]
  simp only [pointMatrixProduct,Int.cast_sum,Int.cast_mul,Finset.sum_div]
  apply sum_congr rfl
  intro k _
  field_simp

theorem pointMatrixOperator_defect_basis {S : ℕ} (hS : 0<S)
    (A B : PointMatrix) (j i : Fin 6) :
    (pointMatrixOperator S A*pointMatrixOperator S B-1) (coordinateBasis j) i=
      (pointMatrixDefect S A B j i:ℝ)/(S:ℝ)^2 := by
  have hs : (S:ℝ)≠0 := ne_of_gt (by exact_mod_cast hS)
  simp only [sub_apply,Pi.sub_apply,pointMatrixOperator_product_basis hS]
  change (pointMatrixProduct A B j i:ℝ)/(S:ℝ)^2-(coordinateBasis j) i=_
  by_cases hij : i=j
  · simp [coordinateBasis,hij,pointMatrixDefect]
    field_simp
  · simp [coordinateBasis,hij,pointMatrixDefect]

theorem pointMatrixOperator_defect_norm {S : ℕ} (hS : 0<S)
    (A B : PointMatrix) {E : ℤ} (hE : 0≤E)
    (hrow : ∀i,∑j : Fin 6,|pointMatrixDefect S A B j i|≤E) :
    ‖pointMatrixOperator S A*pointMatrixOperator S B-1‖≤(E:ℝ)/(S:ℝ)^2 := by
  have hs : 0≤(S:ℝ)^2 := sq_nonneg _
  apply operator_norm_le_row_sum _ (div_nonneg (by exact_mod_cast hE) hs)
  intro i
  have hr : (∑j : Fin 6,|(pointMatrixDefect S A B j i:ℝ)|)≤(E:ℝ) := by exact_mod_cast hrow i
  simp only [pointMatrixOperator_defect_basis hS,abs_div,abs_of_nonneg hs,←Finset.sum_div]
  exact div_le_div_of_nonneg_right hr hs

theorem pointMatrix_inverse_certificate {S : ℕ} (hS : 0<S)
    (B C : PointMatrix) {K E : ℤ} (hK : 0≤K) (hE : 0≤E)
    (hC : ∀i,∑j : Fin 6,|C j i|≤K)
    (hleft : ∀i,∑j : Fin 6,|pointMatrixDefect S C B j i|≤E)
    (hright : ∀i,∑j : Fin 6,|pointMatrixDefect S B C j i|≤E)
    (hq : (E:ℝ)/(S:ℝ)^2<1) :
    IsUnit (pointMatrixOperator S B) ∧
      ‖Ring.inverse (pointMatrixOperator S B)‖≤
        (1/(1-(E:ℝ)/(S:ℝ)^2))*((K:ℝ)/(S:ℝ)) := by
  have hs : (0:ℝ)≤S := Nat.cast_nonneg _
  exact flowEnd_inverse_of_two_defects _ _ hq (div_nonneg (by exact_mod_cast hK) hs)
    (pointMatrixOperator_norm hS C hK hC)
    (pointMatrixOperator_defect_norm hS C B hE hleft)
    (pointMatrixOperator_defect_norm hS B C hE hright)

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.pointMatrix_inverse_certificate
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Exact integer full-matrix inverse certificate audited."

end
