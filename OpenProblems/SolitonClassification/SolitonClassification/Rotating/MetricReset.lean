import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Lean.Util.CollectAxioms

/-! Exact change of error coordinates at a reference-matrix reset.
This is a generic proved lemma about actual linear equivalences, not a
claim that the external numerical matrices satisfy its hypotheses. -/
namespace SolitonClassification.Rotating
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem metric_reset_identity (old new : E ≃L[ℝ] E) (w d : E) :
    new.symm (old w+d)=w+new.symm (old w-new w)+new.symm d := by
  rw [map_add,map_sub,new.symm_apply_apply]
  abel

theorem metric_reset_bound (old new : E ≃L[ℝ] E) (w d : E)
    {I δ ε : ℝ} (hI : 0≤I)
    (hinv : ‖new.symm.toContinuousLinearMap‖≤I)
    (hjump : ‖old.toContinuousLinearMap-new.toContinuousLinearMap‖≤δ)
    (hd : ‖d‖≤ε) :
    ‖new.symm (old w+d)‖≤(1+I*δ)*‖w‖+I*ε := by
  rw [metric_reset_identity]
  have hm : ‖old w-new w‖≤δ*‖w‖ := by
    have h := (old.toContinuousLinearMap-new.toContinuousLinearMap).le_opNorm w
    exact h.trans (mul_le_mul_of_nonneg_right hjump (norm_nonneg w))
  have h1 : ‖new.symm (old w-new w)‖≤I*(δ*‖w‖) := by
    exact (new.symm.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul hinv hm (norm_nonneg _) hI)
  have h2 : ‖new.symm d‖≤I*ε := by
    exact (new.symm.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul hinv hd (norm_nonneg _) hI)
  have h3 := norm_add_le w (new.symm (old w-new w))
  have h4 := norm_add_le (w+new.symm (old w-new w)) (new.symm d)
  nlinarith

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.metric_reset_bound

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
  logInfo "Rotating metric-reset audit passed; standard axioms only."
