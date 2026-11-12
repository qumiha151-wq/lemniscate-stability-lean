import CentroidEscape.Shard_b_plus_s0000_n0050_bounded_Block0008
import CentroidEscape.Shard_b_plus_s0000_n0050_bounded_Block0009

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0000_n0050_bounded.Merge000_0004
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue : Block0008.endpointData=Block0009.inputData := by decide +kernel

theorem boundary : ∀ i : Fin 7,
    (Block0008.stages 5).coefficient 0 i=(Block0009.stages 0).coefficient 0 i := by
  intro i
  rw [Block0008.terminalCoefficient,Block0009.initialCoefficient,glue]

noncomputable def inputData : Vector FixedBall 7 := Block0008.inputData
noncomputable def endpointData : Vector FixedBall 7 := Block0009.endpointData
noncomputable def stages : ℕ → FixedTaylorState :=
  appendTaylorStages 5 Block0008.stages Block0009.stages

theorem checked : Order60SegmentValid mesh stepTime 10 stages :=
  Order60SegmentValid.append Block0008.checked Block0009.checked boundary

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change (appendTaylorStages 5 Block0008.stages Block0009.stages 0).coefficient 0 i=Block0008.inputData[i.val]
  rw [appendTaylorStages_initial (by decide)]
  exact Block0008.initialCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 10).coefficient 0 i=endpointData[i.val] := by
  change (appendTaylorStages 5 Block0008.stages Block0009.stages (5+5)).coefficient 0 i=Block0009.endpointData[i.val]
  rw [appendTaylorStages_terminal]
  exact Block0009.terminalCoefficient i

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0000_n0050_bounded.Merge000_0004
