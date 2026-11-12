import CentroidEscape.Shard_b_minus_s0000_n0050_bounded_Block0002
import CentroidEscape.Shard_b_minus_s0000_n0050_bounded_Block0003

namespace CentroidEscape.CertificateShards.Shard_b_minus_s0000_n0050_bounded.Merge000_0001
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue : Block0002.endpointData=Block0003.inputData := by decide +kernel

theorem boundary : ∀ i : Fin 7,
    (Block0002.stages 5).coefficient 0 i=(Block0003.stages 0).coefficient 0 i := by
  intro i
  rw [Block0002.terminalCoefficient,Block0003.initialCoefficient,glue]

noncomputable def inputData : Vector FixedBall 7 := Block0002.inputData
noncomputable def endpointData : Vector FixedBall 7 := Block0003.endpointData
noncomputable def stages : ℕ → FixedTaylorState :=
  appendTaylorStages 5 Block0002.stages Block0003.stages

theorem checked : Order60SegmentValid mesh stepTime 10 stages :=
  Order60SegmentValid.append Block0002.checked Block0003.checked boundary

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change (appendTaylorStages 5 Block0002.stages Block0003.stages 0).coefficient 0 i=Block0002.inputData[i.val]
  rw [appendTaylorStages_initial (by decide)]
  exact Block0002.initialCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 10).coefficient 0 i=endpointData[i.val] := by
  change (appendTaylorStages 5 Block0002.stages Block0003.stages (5+5)).coefficient 0 i=Block0003.endpointData[i.val]
  rw [appendTaylorStages_terminal]
  exact Block0003.terminalCoefficient i

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_minus_s0000_n0050_bounded.Merge000_0001
