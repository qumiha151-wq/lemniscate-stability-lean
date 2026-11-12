import CentroidEscape.Shard_a_plus_s0550_n0050_bounded_Merge002_0000
import CentroidEscape.Shard_a_plus_s0550_n0050_bounded_Merge000_0004

namespace CentroidEscape.CertificateShards.Shard_a_plus_s0550_n0050_bounded.Merge003_0000
open MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem glue : Merge002_0000.endpointData=Merge000_0004.inputData := by decide +kernel

theorem boundary : ∀ i : Fin 7,
    (Merge002_0000.stages 40).coefficient 0 i=(Merge000_0004.stages 0).coefficient 0 i := by
  intro i
  rw [Merge002_0000.terminalCoefficient,Merge000_0004.initialCoefficient,glue]

noncomputable def inputData : Vector FixedBall 7 := Merge002_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := Merge000_0004.endpointData
noncomputable def stages : ℕ → FixedTaylorState :=
  appendTaylorStages 40 Merge002_0000.stages Merge000_0004.stages

theorem checked : Order60SegmentValid mesh stepTime 50 stages :=
  Order60SegmentValid.append Merge002_0000.checked Merge000_0004.checked boundary

theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change (appendTaylorStages 40 Merge002_0000.stages Merge000_0004.stages 0).coefficient 0 i=Merge002_0000.inputData[i.val]
  rw [appendTaylorStages_initial (by decide)]
  exact Merge002_0000.initialCoefficient i

theorem terminalCoefficient (i : Fin 7) : (stages 50).coefficient 0 i=endpointData[i.val] := by
  change (appendTaylorStages 40 Merge002_0000.stages Merge000_0004.stages (40+10)).coefficient 0 i=Merge000_0004.endpointData[i.val]
  rw [appendTaylorStages_terminal]
  exact Merge000_0004.terminalCoefficient i

attribute [irreducible] stages
end CentroidEscape.CertificateShards.Shard_a_plus_s0550_n0050_bounded.Merge003_0000
