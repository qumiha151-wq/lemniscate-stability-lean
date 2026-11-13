module

public import SolitonClassification.Rotating.FlowMetricDiscrete

@[expose] public section

/-! Rational sufficient budgets for exp(budget)-1<=δrel. These lemmas
permit exact rational interval arithmetic rather than an assumed
transcendental evaluation. They do not assert any candidate's budget. -/
namespace SolitonClassification.Rotating
noncomputable section

theorem exp_deviation_budget {b δrel : ℝ} (hq : 0≤δrel) (hb : b≤δrel/(1+δrel)) :
    Real.exp b≤1+δrel := by
  have hp : 0<1+δrel := by linarith
  have ht0 : 0≤δrel/(1+δrel) := div_nonneg hq hp.le
  have ht1 : δrel/(1+δrel)<1 := (div_lt_iff₀ hp).mpr (by linarith)
  have he := Real.exp_bound_div_one_sub_of_interval ht0 ht1
  have hm : (1+δrel)*(1-δrel/(1+δrel))=1 := by
    field_simp
    ring
  apply (Real.exp_le_exp.mpr hb).trans
  exact he.trans ((div_le_iff₀ (sub_pos.mpr ht1)).mpr hm.ge)

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating rational deviation-budget audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating rational deviation-budget audit passed for {count} declarations."
