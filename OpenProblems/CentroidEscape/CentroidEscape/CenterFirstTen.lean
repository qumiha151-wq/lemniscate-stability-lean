import CentroidEscape.CenterBlock000
import CentroidEscape.CenterBlock005

namespace CentroidEscape.CenterBlockData.FirstTen
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem boundary : ∀ i : Fin 7,
    (Block000.stages 5).coefficient 0 i=(Block005.stages 0).coefficient 0 i := by
  intro i
  change Step004.endpointData[i.val]=Step005.stepData.coefficient 0 i
  rw [Step005.inputCoefficient]
  have he : Step004.endpointData=Step005.inputData := by decide +kernel
  rw [he]

noncomputable def stages : ℕ → FixedTaylorState :=
  appendTaylorStages 5 Block000.stages Block005.stages

theorem checked : Order60SegmentValid mesh stepTime 10 stages :=
  Order60SegmentValid.append Block000.checked Block005.checked boundary

end CentroidEscape.CenterBlockData.FirstTen

#print axioms CentroidEscape.CenterBlockData.FirstTen.checked

open Lean Elab Command in
run_cmd do
  let target := `CentroidEscape.CenterBlockData.FirstTen.checked
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for axiomName in (← collectAxioms target) do
    unless allowed.contains axiomName do
      throwError "Concrete first-ten audit failed: {target} depends on {axiomName}"
  logInfo "Concrete first-ten audit passed: 600 Taylor stages, 10 endpoints and input margins, 9 glues; standard axioms only."
