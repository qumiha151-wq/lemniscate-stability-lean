import CentroidEscape.CenterFirstEleven
import CentroidEscape.Shard_center_s0011_n0005_bounded_Block0000

/-! Actual boundary agreement connects the frozen eleven-step prefix to the newly checked five-step shard. -/
namespace CentroidEscape.CenterCompactData.FirstSixteen
open MetricStability CenterBlockData
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

noncomputable def tailStages : ℕ → FixedTaylorState :=
  CertificateShards.Shard_center_s0011_n0005_bounded.Block0000.stages

theorem boundary : ∀ i : Fin 7,
    (FirstEleven.stages 11).coefficient 0 i=(tailStages 0).coefficient 0 i := by
  intro i
  change Step010.endpointData[i.val]=
    (CertificateShards.Shard_center_s0011_n0005_bounded.Block0000.stages 0).coefficient 0 i
  rw [CertificateShards.Shard_center_s0011_n0005_bounded.Block0000.initialCoefficient]
  have he : Step010.endpointData=
      CertificateShards.Shard_center_s0011_n0005_bounded.Block0000.inputData := by
    decide +kernel
  rw [he]

noncomputable def stages : ℕ → FixedTaylorState :=
  appendTaylorStages 11 FirstEleven.stages tailStages

theorem checked : Order60SegmentValid mesh stepTime 16 stages :=
  Order60SegmentValid.append FirstEleven.checked
    CertificateShards.Shard_center_s0011_n0005_bounded.Block0000.checked boundary

end CentroidEscape.CenterCompactData.FirstSixteen

#print axioms CentroidEscape.CenterCompactData.FirstSixteen.checked

open Lean Elab Command in
run_cmd do
  let target := `CentroidEscape.CenterCompactData.FirstSixteen.checked
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for axiomName in (← collectAxioms target) do
    unless allowed.contains axiomName do
      throwError "First-sixteen audit failed: {target} depends on {axiomName}"
  logInfo "First-sixteen transitive strict audit passed."
