import CentroidEscape.Shard_center_s0400_n0050_bounded_Block0000
import CentroidEscape.Shard_center_s0400_n0050_bounded_Block0001

namespace CentroidEscape.CertificateShards.Shard_center_s0400_n0050_bounded.Merge000_0000
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue : Block0000.endpointData=Block0001.inputData := by decide +kernel

theorem boundary : ∀ i : Fin 7,
    (Block0000.stages 5).coefficient 0 i=(Block0001.stages 0).coefficient 0 i := by
  intro i
  rw [Block0000.terminalCoefficient,Block0001.initialCoefficient,glue]

noncomputable def inputData : Vector FixedBall 7 := Block0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := Block0001.endpointData
noncomputable def stages : ℕ → FixedTaylorState :=
  appendTaylorStages 5 Block0000.stages Block0001.stages

theorem checked : Order60SegmentValid mesh stepTime 10 stages :=
  Order60SegmentValid.append Block0000.checked Block0001.checked boundary

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change (appendTaylorStages 5 Block0000.stages Block0001.stages 0).coefficient 0 i=Block0000.inputData[i.val]
  rw [appendTaylorStages_initial (by decide)]
  exact Block0000.initialCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 10).coefficient 0 i=endpointData[i.val] := by
  change (appendTaylorStages 5 Block0000.stages Block0001.stages (5+5)).coefficient 0 i=Block0001.endpointData[i.val]
  rw [appendTaylorStages_terminal]
  exact Block0001.terminalCoefficient i

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0400_n0050_bounded.Merge000_0000
