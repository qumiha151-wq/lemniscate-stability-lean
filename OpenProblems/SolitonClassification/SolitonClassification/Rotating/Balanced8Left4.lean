import SolitonClassification.Rotating.Block8Leaf00
import SolitonClassification.Rotating.Block8Leaf01Matrix
import SolitonClassification.Rotating.Block8Leaf02Matrix
import SolitonClassification.Rotating.Block8Leaf03Matrix
import SolitonClassification.Rotating.PolynomialPointGridBlock

namespace SolitonClassification.Rotating.Balanced8Left4
noncomputable section
open Candidate
set_option Elab.async false
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def state (j : ℕ) : State := Block8Nodes.state (0+j)
def matrix (j : ℕ) : FlowEnd := Block8Nodes.operator (0+j)

theorem state_reset (j : ℕ) (hj : j<4) :
    ‖polynomialPath (taylorPolynomial (state j) 42) (1*(step:ℝ))-state (j+1)‖≤1/10^55 := by
  interval_cases j
  · simpa only [state,Nat.reduceAdd,one_mul] using Block8Leaf00.state_reset
  · simpa only [state,Nat.reduceAdd,one_mul] using Block8Leaf01State.state_reset
  · simpa only [state,Nat.reduceAdd,one_mul] using Block8Leaf02State.state_reset
  · simpa only [state,Nat.reduceAdd,one_mul] using Block8Leaf03State.state_reset

theorem matrix_reset (j : ℕ) (hj : j<4) :
    ‖referencePolynomialMatrix 1 (state j) 22 (matrix j) (step:ℝ)-matrix (j+1)‖≤1/10^55 := by
  interval_cases j
  · simpa only [state,matrix,Nat.reduceAdd] using Block8Leaf00.matrix_reset
  · simpa only [state,matrix,Nat.reduceAdd] using Block8Leaf01Matrix.matrix_reset
  · simpa only [state,matrix,Nat.reduceAdd] using Block8Leaf02Matrix.matrix_reset
  · simpa only [state,matrix,Nat.reduceAdd] using Block8Leaf03Matrix.matrix_reset

def certificate : PolynomialPointGridBlock 1 (step:ℝ) (1/10^55) (1/10^55) 4 where
  state := state
  matrix := matrix
  inner j hj := Block8Nodes.inner (0+j) (by omega)
  nodeUnit j hj := (Block8Nodes.bounds (0+j) (by omega)).2.1
  nodeNorm j hj := (Block8Nodes.bounds (0+j) (by omega)).1
  nodeInverse j hj := (Block8Nodes.bounds (0+j) (by omega)).2.2
  stateResetNonneg := by norm_num
  matrixResetNonneg := by norm_num
  stateReset := state_reset
  matrixReset := matrix_reset

theorem state_start : certificate.state 0=Block8Nodes.state 0 := rfl
theorem matrix_start : certificate.matrix 0=Block8Nodes.operator 0 := rfl
theorem state_last : certificate.state 4=Block8Nodes.state 4 := rfl
theorem matrix_last : certificate.matrix 4=Block8Nodes.operator 4 := rfl

attribute [irreducible] certificate
end
end SolitonClassification.Rotating.Balanced8Left4

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Balanced pilot audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Balanced pilot audited: {count} declarations; standard axioms only."
