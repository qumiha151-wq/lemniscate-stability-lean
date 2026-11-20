import SolitonClassification.ReflectedNumericGeometry
import SolitonClassification.Reflected.FirstRoot
import Lean.Util.CollectAxioms

namespace ClosedSimilarity.ReflectedArc

/-- Unconditional existence of a smooth zero-turn homothetic expander with
the certified non-Bernoulli centre marker and a genuine pure-normal flow. -/
theorem exists_first_zero_turn_expander : ∃ b T : ℝ, FirstProfile b T := by
  obtain ⟨b,hb,T,hT,hv,hq,tube⟩ := SolitonClassification.Reflected.first_reflected_shooting_zero
  exact ⟨b,T,firstProfile_of_zero hb hT hv hq tube⟩

end ClosedSimilarity.ReflectedArc

open Lean Elab Command in
run_cmd do
  let n := `ClosedSimilarity.ReflectedArc.exists_first_zero_turn_expander
  for a in (← collectAxioms n) do
    unless #[`propext,`Classical.choice,`Quot.sound].contains a do
      throwError "Unexpected axiom {a} in {n}"
  logInfo m!"Unconditional reflected expander verified: {n}"

#print axioms ClosedSimilarity.ReflectedArc.exists_first_zero_turn_expander
