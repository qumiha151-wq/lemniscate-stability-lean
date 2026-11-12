import SolitonClassification.Rotating.MatrixRowNorm
import SolitonClassification.Rotating.BenchState60
import SolitonClassification.Rotating.BenchMatrix22
import SolitonClassification.Rotating.FlowTube
import SolitonClassification.Rotating.ReferenceInversePerturbation

/-! Exact rational midpoint nodes for the two-segment prototype. A new
segment starts at these point values; preceding interval radii are charged
to explicit reset jumps, not silently carried as exact initial values. -/
namespace SolitonClassification.Rotating.GridReset
noncomputable section
open Candidate
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rawState1 (i : Fin 6) : ℚ := (BenchState60.endpointData[i.val].center:ℚ)/mesh
def state1 : State := fun i=>(rawState1 i:ℝ)
def rawMatrix1 (j i : Fin 6) : ℚ := ((BenchMatrix22.fullEndpoint j)[i.val].center:ℚ)/mesh
def matrix1 : FlowEnd := rationalColumnOperator rawMatrix1
def pointState1 (i : Fin 6) : FixedBall := ⟨BenchState60.endpointData[i.val].center,0⟩
def pointMatrix1 (j i : Fin 6) : FixedBall := ⟨(BenchMatrix22.fullEndpoint j)[i.val].center,0⟩

theorem pointState1_contains (i : Fin 6) : (pointState1 i).Contains mesh (state1 i) := by
  simp [pointState1,state1,rawState1,FixedBall.Contains,FixedBall.toRational,RationalBall.Contains]

theorem pointMatrix1_contains (j i : Fin 6) : (pointMatrix1 j i).Contains mesh (matrix1 (coordinateBasis j) i) := by
  simp [pointMatrix1,matrix1,rationalColumnOperator,columnOperator_basis,rawMatrix1,
    FixedBall.Contains,FixedBall.toRational,RationalBall.Contains]

theorem state1_checked : |rawState1 0|≤407/50 ∧ |rawState1 1|≤33/8 ∧
    |rawState1 2|≤731/100 ∧ |rawState1 3|≤731/100 ∧ |rawState1 4|≤1/100 := by decide +kernel

theorem state1_mem_innerTube : state1∈innerTube := by
  change |(rawState1 0:ℝ)|≤407/50 ∧ |(rawState1 1:ℝ)|≤33/8 ∧
    |(rawState1 2:ℝ)|≤731/100 ∧ |(rawState1 3:ℝ)|≤731/100 ∧ |(rawState1 4:ℝ)|≤1/100
  have lift (q r : ℚ) (h : |q|≤r) : |(q:ℝ)|≤(r:ℝ) := by
    rw [←Rat.cast_abs]
    exact Rat.cast_le.mpr h
  rcases state1_checked with ⟨h0,h1,h2,h3,h4⟩
  exact ⟨by simpa only [Rat.cast_div,Rat.cast_ofNat] using lift _ _ h0,
    by simpa only [Rat.cast_div,Rat.cast_ofNat] using lift _ _ h1,
    by simpa only [Rat.cast_div,Rat.cast_ofNat] using lift _ _ h2,
    by simpa only [Rat.cast_div,Rat.cast_ofNat] using lift _ _ h3,
    by simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using lift _ _ h4⟩

theorem matrix1_rows_checked : ∀i : Fin 6,∑j : Fin 6,|rawMatrix1 j i|≤2 := by decide +kernel
theorem matrix1_identity_rows_checked : ∀i : Fin 6,
    ∑j : Fin 6,|rawMatrix1 j i-(if i=j then 1 else 0)|≤1/2 := by decide +kernel

theorem matrix1_norm : ‖matrix1‖≤2 := by
  convert! rationalColumnOperator_norm_le rawMatrix1 (by norm_num) matrix1_rows_checked using 1

theorem matrix1_identity_error : ‖matrix1-1‖≤1/2 := by
  convert! rationalColumnOperator_sub_one_norm_le rawMatrix1 (by norm_num) matrix1_identity_rows_checked using 1
  norm_num

theorem matrix1_inverse : IsUnit matrix1 ∧ ‖Ring.inverse matrix1‖≤2 := by
  have h := flowEnd_inverse_bound_of_norm_sub_one_le matrix1 matrix1_identity_error (by norm_num)
  norm_num at h
  exact h

end
end SolitonClassification.Rotating.GridReset

#print axioms SolitonClassification.Rotating.GridReset.matrix1_inverse
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "First exact midpoint state and full matrix nodes checked."
