import CentroidEscape.Shard_a_plus_s0500_n0050_bounded_Merge000_0000
import CentroidEscape.Shard_a_plus_s0500_n0050_bounded_Merge000_0001

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0500_n0050_bounded.Merge001_0000
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue : Merge000_0000.endpointData=Merge000_0001.inputData := by decide +kernel

theorem boundary : ∀ i : Fin 7,
    (Merge000_0000.stages 10).coefficient 0 i=(Merge000_0001.stages 0).coefficient 0 i := by
  intro i
  rw [Merge000_0000.terminalCoefficient,Merge000_0001.initialCoefficient,glue]

noncomputable def inputData : Vector FixedBall 7 := Merge000_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := Merge000_0001.endpointData
noncomputable def stages : ℕ → FixedTaylorState :=
  appendTaylorStages 10 Merge000_0000.stages Merge000_0001.stages

theorem checked : Order60SegmentValid mesh stepTime 20 stages :=
  Order60SegmentValid.append Merge000_0000.checked Merge000_0001.checked boundary

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change (appendTaylorStages 10 Merge000_0000.stages Merge000_0001.stages 0).coefficient 0 i=Merge000_0000.inputData[i.val]
  rw [appendTaylorStages_initial (by decide)]
  exact Merge000_0000.initialCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 20).coefficient 0 i=endpointData[i.val] := by
  change (appendTaylorStages 10 Merge000_0000.stages Merge000_0001.stages (10+10)).coefficient 0 i=Merge000_0001.endpointData[i.val]
  rw [appendTaylorStages_terminal]
  exact Merge000_0001.terminalCoefficient i

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0500_n0050_bounded.Merge001_0000
