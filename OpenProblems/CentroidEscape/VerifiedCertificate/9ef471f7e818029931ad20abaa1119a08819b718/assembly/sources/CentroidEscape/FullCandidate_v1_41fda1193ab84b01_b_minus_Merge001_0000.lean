import CentroidEscape.FullCandidate_v1_41fda1193ab84b01_b_minus_Merge000_0000
import CentroidEscape.FullCandidate_v1_41fda1193ab84b01_b_minus_Merge000_0001

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge001_0000
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem glue : CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0000.endpointData=CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0001.inputData := by decide +kernel
theorem boundary : ∀ i : Fin 7,
    (CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0000.stages 100).coefficient 0 i=(CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0001.stages 0).coefficient 0 i := by
  intro i
  rw [CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0000.terminalCoefficient,CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0001.initialCoefficient,glue]
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0000.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0001.endpointData
noncomputable def stages : ℕ → FixedTaylorState := appendTaylorStages 100 CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0000.stages CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0001.stages
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 200 stages :=
  Order60SegmentValid.append CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0000.checked CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0001.checked boundary
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change (appendTaylorStages 100 CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0000.stages CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0001.stages 0).coefficient 0 i=CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0000.inputData[i.val]
  rw [appendTaylorStages_initial (by decide)]
  exact CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0000.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 200).coefficient 0 i=endpointData[i.val] := by
  change (appendTaylorStages 100 CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0000.stages CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0001.stages (100+100)).coefficient 0 i=CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0001.endpointData[i.val]
  rw [appendTaylorStages_terminal]
  exact CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0001.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge001_0000
