import SolitonClassification.Rotating.RotatingGridMargin
import SolitonClassification.Rotating.UniversalStateOrders

/-! Exact scalar-cap budgets supply the generic reference margin at any
state order. The 42/44 instances keep the frozen order60 theory intact. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set UniversalMajorant

theorem taylorPolynomial_order_margin {a : State} (ha : a∈innerTube)
    {N : ℕ} {ε : ℚ} (hε : ε≤1) (hb : stateResidualAtCap N≤ε)
    (hex : (19/2)*(stateScalarValueAtCap N-1)≤129/250) {t : ℝ}
    (ht : |t|≤(universalStepCap:ℝ)) :
    outerTubeMargin (polynomialPath (taylorPolynomial a N) t) (1/100) := by
  apply taylorPolynomial_margin_of_coarse ha N universalStepCap_pos.le universalStepCap_le_local
    (fun s hs => (taylorPolynomial_excursion ha N s).trans
      (stateDisplacement_order_uniform hex (abs_nonneg s) hs)) _ ht
  intro s hs
  exact (taylorResidual_order_uniform ha hb hs).trans (by exact_mod_cast hε)

theorem taylorPolynomial42_margin_uniform {a : State} (ha : a∈innerTube) {t : ℝ}
    (ht : |t|≤(universalStepCap:ℝ)) :
    outerTubeMargin (polynomialPath (taylorPolynomial a 42) t) (1/100) :=
  taylorPolynomial_order_margin ha (by norm_num : (6:ℚ)/10^40≤1)
    stateOrder42_budget.1.2 stateOrder42_budget.2 ht

theorem taylorPolynomial44_margin_uniform {a : State} (ha : a∈innerTube) {t : ℝ}
    (ht : |t|≤(universalStepCap:ℝ)) :
    outerTubeMargin (polynomialPath (taylorPolynomial a 44) t) (1/100) :=
  taylorPolynomial_order_margin ha (by norm_num : (6:ℚ)/10^42≤1)
    stateOrder44_budget.1.2 stateOrder44_budget.2 ht

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating lower-order reference-margin audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating lower-order reference-margin audit passed for {count} declarations."
