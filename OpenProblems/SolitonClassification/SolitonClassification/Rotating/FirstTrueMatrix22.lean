import SolitonClassification.Rotating.ReferencePolynomialMatrix22
import SolitonClassification.Rotating.BenchMatrix22
import SolitonClassification.Rotating.FirstTrueState60

/-! All 36 concrete first-segment entries now enclose the actual initial
derivative of supportFlow. Finite kernel checks and the actual operator
tail are combined; this remains a first segment, not a global orbit. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Candidate UniversalMajorant
set_option Elab.async false
set_option maxRecDepth 100000

def FixedBall.widenBy (b : FixedBall) (r : ℤ) : FixedBall := ⟨b.center,b.radius+r⟩

theorem FixedBall.contains_widenBy {S : ℕ} {b : FixedBall} {r : ℤ} {x y : ℝ}
    (hy : b.Contains S y) (hxy : |x-y|≤(r:ℝ)/(S:ℝ)) : (b.widenBy r).Contains S x := by
  simp only [FixedBall.Contains,FixedBall.toRational,RationalBall.Contains,
    FixedBall.widenBy,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,Int.cast_add,Rat.cast_add] at *
  calc
    _ ≤ |x-y|+|y-(b.center:ℝ)/S| := abs_sub_le _ _ _
    _ ≤ (r:ℝ)/(S:ℝ)+(b.radius:ℝ)/S := add_le_add hxy hy
    _ = _ := by ring

theorem first_matrix_basis_norm (j : Fin 6) : ‖BenchMatrix22.basis j‖=1 := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    by_cases h : i=j <;> simp [BenchMatrix22.basis,h]
  · simpa [BenchMatrix22.basis] using coordinate_bound (BenchMatrix22.basis j) j

def firstMatrixTailUnits : ℤ := 4*10^39

theorem first_matrix_step_mem : (step:ℝ)∈Icc 0 (universalStepCap:ℝ) := by
  refine ⟨(Rat.cast_pos.mpr positive_step).le,?_⟩
  change (step:ℝ)≤(stepCap:ℝ)
  exact Rat.cast_le.mpr step_below_cap.le

theorem first_true_matrix22_endpoint (j i : Fin 6) :
    ((BenchMatrix22.fullEndpoint j)[i.val].widenBy firstMatrixTailUnits).Contains mesh
      (fderiv ℝ (supportFlow 1 (by norm_num) (step:ℝ)) initial (BenchMatrix22.basis j) i) := by
  apply FixedBall.contains_widenBy (BenchMatrix22.full_matrix_enclosed j i)
  have h := universal_signed_trueVariation60_22_error 1 (by norm_num)
    FirstResidualInteger60.initial_mem_innerTube (BenchMatrix22.basis j) first_matrix_step_mem
  have h' : ‖fderiv ℝ (supportFlow 1 (by norm_num) (step:ℝ)) initial (BenchMatrix22.basis j)-
      polynomialPath (variationPolynomial initial (BenchMatrix22.basis j) 22) (step:ℝ)‖≤(4:ℝ)/10^21 := by
    simpa only [one_mul,first_matrix_basis_norm] using h
  have hc : (firstMatrixTailUnits:ℝ)/(mesh:ℝ)=(4:ℝ)/10^21 := by
    norm_num [firstMatrixTailUnits,mesh]
  rw [hc]
  exact (coordinate_bound
    (fderiv ℝ (supportFlow 1 (by norm_num) (step:ℝ)) initial (BenchMatrix22.basis j)-
      polynomialPath (variationPolynomial initial (BenchMatrix22.basis j) 22) (step:ℝ)) i).trans h'

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.first_true_matrix22_endpoint
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Concrete actual first 6-by-6 matrix endpoint audit passed for {count} declarations."
