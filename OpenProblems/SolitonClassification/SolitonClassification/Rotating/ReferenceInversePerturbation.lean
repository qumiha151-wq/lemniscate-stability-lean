import SolitonClassification.Rotating.FlowMetricCoordinates
import Mathlib.Analysis.Normed.Ring.Units

/-! Quantitative Neumann inversion for real reference endomorphisms.
The hypothesis is an actual operator-norm bound, not a matrix-entry bound.
No numerical inverse is silently identified with Ring.inverse. -/
namespace SolitonClassification.Rotating
noncomputable section

theorem flowEnd_inverse_bound_of_norm_one_sub_le (U : FlowEnd) {q : ℝ}
    (hbound : ‖(1:FlowEnd)-U‖≤q) (hq : q<1) :
    IsUnit U ∧ ‖Ring.inverse U‖≤1/(1-q) := by
  have hu : ‖(1:FlowEnd)-U‖<1 := hbound.trans_lt hq
  have he : (1:FlowEnd)-(1-U)=U := by abel
  have hunit : IsUnit U := by
    have h := (Units.oneSub ((1:FlowEnd)-U) hu).isUnit
    simpa only [Units.val_oneSub,he] using h
  refine ⟨hunit,?_⟩
  have hinv : Ring.inverse U=∑'n : ℕ,((1:FlowEnd)-U)^n := by
    calc
      Ring.inverse U=Ring.inverse ((1:FlowEnd)-(1-U)) := congrArg Ring.inverse he.symm
      _ = _ := NormedRing.inverse_one_sub _ hu
  rw [hinv]
  apply (tsum_geometric_le_of_norm_lt_one ((1:FlowEnd)-U) hu).trans
  rw [norm_one,sub_self,zero_add,one_div]
  exact inv_anti₀ (sub_pos.mpr hq) (sub_le_sub_left hbound 1)

theorem flowEnd_inverse_bound_of_norm_sub_one_le (U : FlowEnd) {q : ℝ}
    (hbound : ‖U-(1:FlowEnd)‖≤q) (hq : q<1) :
    IsUnit U ∧ ‖Ring.inverse U‖≤1/(1-q) :=
  flowEnd_inverse_bound_of_norm_one_sub_le U (by simpa only [norm_sub_rev] using hbound) hq

theorem flowEnd_inverse_bound_one_fifth (U : FlowEnd)
    (hbound : ‖U-(1:FlowEnd)‖≤1/5) :
    IsUnit U ∧ ‖Ring.inverse U‖≤5/4 := by
  have h:=flowEnd_inverse_bound_of_norm_sub_one_le U hbound (by norm_num)
  norm_num at h
  exact h

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.flowEnd_inverse_bound_of_norm_one_sub_le
open Lean Elab Command in
run_cmd do
  for (name, _) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Reference endomorphism Neumann inverse audited; standard axioms only."
