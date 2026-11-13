module

public import SolitonClassification.Rotating.MatrixRowNorm
public import SolitonClassification.Rotating.FixedBall

@[expose] public section

/-! An outward-rounded endpoint interval is replaced by its exact
midpoint only after charging its radius as a reset defect. The matrix
statement sums the six coordinate errors in each row. -/
namespace SolitonClassification.Rotating
noncomputable section
open Finset
set_option Elab.async false

def fixedStateMidpoint (S : ℕ) (e : Fin 6 → FixedBall) : State :=
  fun i=>(((e i).center:ℚ)/S:ℚ)

def fixedMatrixMidpoint (S : ℕ) (e : Fin 6 → Fin 6 → FixedBall) : State →L[ℝ] State :=
  rationalColumnOperator (fun j i=>((e j i).center:ℚ)/S)

theorem fixedStateMidpoint_error {S : ℕ} {e : Fin 6 → FixedBall} {x : State}
    (h : ∀i,(e i).Contains S (x i)) {δ : ℚ} (hδ : 0≤δ)
    (hr : ∀i,((e i).radius:ℚ)/S≤δ) : ‖x-fixedStateMidpoint S e‖≤(δ:ℝ) := by
  rw [pi_norm_le_iff_of_nonneg (Rat.cast_nonneg.mpr hδ)]
  intro i
  have hc := h i
  change |x i-((((e i).center:ℚ)/S:ℚ):ℝ)|≤((((e i).radius:ℚ)/S:ℚ):ℝ) at hc
  exact hc.trans (Rat.cast_le.mpr (hr i))

theorem fixedMatrixMidpoint_error {S : ℕ} {e : Fin 6 → Fin 6 → FixedBall}
    {A : State →L[ℝ] State} (h : ∀j i,(e j i).Contains S (A (coordinateBasis j) i))
    {δ : ℚ} (hδ : 0≤δ) (hr : ∀i,∑j : Fin 6,((e j i).radius:ℚ)/S≤δ) :
    ‖A-fixedMatrixMidpoint S e‖≤(δ:ℝ) := by
  apply operator_norm_le_row_sum _ (Rat.cast_nonneg.mpr hδ)
  intro i
  have hs : (∑j : Fin 6,((((e j i).radius:ℚ)/S:ℚ):ℝ))≤(δ:ℝ) := by
    exact_mod_cast hr i
  apply le_trans _ hs
  apply sum_le_sum
  intro j _
  have hc := h j i
  change |A (coordinateBasis j) i-((((e j i).center:ℚ)/S:ℚ):ℝ)|≤
    ((((e j i).radius:ℚ)/S:ℚ):ℝ) at hc
  simpa only [sub_apply,Pi.sub_apply,fixedMatrixMidpoint,
    rationalColumnOperator,columnOperator_basis] using hc

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.fixedMatrixMidpoint_error
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Actual state and full matrix midpoint reset defects audited."

end
