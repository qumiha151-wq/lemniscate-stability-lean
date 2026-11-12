import SolitonClassification.Rotating.Block8Nodes

import SolitonClassification.Rotating.Grid42P00Matrix

import SolitonClassification.Rotating.ReferencePolynomialMatrix

namespace SolitonClassification.Rotating.Block8Leaf00

open Candidate

set_option Elab.async false

set_option maxRecDepth 100000

set_option maxHeartbeats 0

set_option backward.isDefEq.respectTransparency false

theorem state_reset : ‖polynomialPath (taylorPolynomial (Block8Nodes.state 0) 42) (step:ℝ)-Block8Nodes.state 1‖≤1/10^55 := by
  rw [Block8Nodes.state_zero,Block8Nodes.state_one]
  exact Grid42P00State.state_reset.trans (by norm_num)

theorem matrix_reset : ‖referencePolynomialMatrix 1 (Block8Nodes.state 0) 22 (Block8Nodes.operator 0) (step:ℝ)-Block8Nodes.operator 1‖≤1/10^55 := by
  rw [Block8Nodes.state_zero,Block8Nodes.operator_zero,Block8Nodes.operator_one]
  simpa only [referencePolynomialMatrix,one_mul] using Grid42P00Matrix.matrix_reset.trans (by norm_num : (1:ℝ)/10^57≤1/10^55)

end SolitonClassification.Rotating.Block8Leaf00

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Block8 concrete leaf audit passed; standard axioms only."
