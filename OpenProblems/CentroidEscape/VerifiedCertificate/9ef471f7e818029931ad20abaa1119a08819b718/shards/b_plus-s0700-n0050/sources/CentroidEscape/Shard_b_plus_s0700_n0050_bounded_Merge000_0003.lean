import CentroidEscape.Shard_b_plus_s0700_n0050_bounded_Block0006
import CentroidEscape.Shard_b_plus_s0700_n0050_bounded_Block0007

namespace CentroidEscape.CertificateShards.Shard_b_plus_s0700_n0050_bounded.Merge000_0003
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue : Block0006.endpointData=Block0007.inputData := by decide +kernel

theorem boundary : ∀ i : Fin 7,
    (Block0006.stages 5).coefficient 0 i=(Block0007.stages 0).coefficient 0 i := by
  intro i
  rw [Block0006.terminalCoefficient,Block0007.initialCoefficient,glue]

noncomputable def inputData : Vector FixedBall 7 := Block0006.inputData
noncomputable def endpointData : Vector FixedBall 7 := Block0007.endpointData
noncomputable def stages : ℕ → FixedTaylorState :=
  appendTaylorStages 5 Block0006.stages Block0007.stages

theorem checked : Order60SegmentValid mesh stepTime 10 stages :=
  Order60SegmentValid.append Block0006.checked Block0007.checked boundary

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change (appendTaylorStages 5 Block0006.stages Block0007.stages 0).coefficient 0 i=Block0006.inputData[i.val]
  rw [appendTaylorStages_initial (by decide)]
  exact Block0006.initialCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 10).coefficient 0 i=endpointData[i.val] := by
  change (appendTaylorStages 5 Block0006.stages Block0007.stages (5+5)).coefficient 0 i=Block0007.endpointData[i.val]
  rw [appendTaylorStages_terminal]
  exact Block0007.terminalCoefficient i

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_b_plus_s0700_n0050_bounded.Merge000_0003
