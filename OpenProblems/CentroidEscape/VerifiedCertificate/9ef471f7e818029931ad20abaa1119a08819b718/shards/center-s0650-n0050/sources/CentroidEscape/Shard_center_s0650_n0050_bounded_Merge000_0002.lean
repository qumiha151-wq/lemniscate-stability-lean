import CentroidEscape.Shard_center_s0650_n0050_bounded_Block0004
import CentroidEscape.Shard_center_s0650_n0050_bounded_Block0005

namespace CentroidEscape.CertificateShards.Shard_center_s0650_n0050_bounded.Merge000_0002
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue : Block0004.endpointData=Block0005.inputData := by decide +kernel

theorem boundary : ∀ i : Fin 7,
    (Block0004.stages 5).coefficient 0 i=(Block0005.stages 0).coefficient 0 i := by
  intro i
  rw [Block0004.terminalCoefficient,Block0005.initialCoefficient,glue]

noncomputable def inputData : Vector FixedBall 7 := Block0004.inputData
noncomputable def endpointData : Vector FixedBall 7 := Block0005.endpointData
noncomputable def stages : ℕ → FixedTaylorState :=
  appendTaylorStages 5 Block0004.stages Block0005.stages

theorem checked : Order60SegmentValid mesh stepTime 10 stages :=
  Order60SegmentValid.append Block0004.checked Block0005.checked boundary

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change (appendTaylorStages 5 Block0004.stages Block0005.stages 0).coefficient 0 i=Block0004.inputData[i.val]
  rw [appendTaylorStages_initial (by decide)]
  exact Block0004.initialCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 10).coefficient 0 i=endpointData[i.val] := by
  change (appendTaylorStages 5 Block0004.stages Block0005.stages (5+5)).coefficient 0 i=Block0005.endpointData[i.val]
  rw [appendTaylorStages_terminal]
  exact Block0005.terminalCoefficient i

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_center_s0650_n0050_bounded.Merge000_0002
