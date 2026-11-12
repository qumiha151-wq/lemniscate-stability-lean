import CentroidEscape.FullCandidate_v1_41fda1193ab84b01_a_minus_Input0002
import CentroidEscape.FullCandidate_v1_41fda1193ab84b01_a_minus_Input0003

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Merge000_0001
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem glue : CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0002.endpointData=CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0003.inputData := by decide +kernel
theorem boundary : ∀ i : Fin 7,
    (CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0002.stages 50).coefficient 0 i=(CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0003.stages 0).coefficient 0 i := by
  intro i
  rw [CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0002.terminalCoefficient,CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0003.initialCoefficient,glue]
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0002.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0003.endpointData
noncomputable def stages : ℕ → FixedTaylorState := appendTaylorStages 50 CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0002.stages CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0003.stages
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 100 stages :=
  Order60SegmentValid.append CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0002.checked CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0003.checked boundary
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change (appendTaylorStages 50 CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0002.stages CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0003.stages 0).coefficient 0 i=CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0002.inputData[i.val]
  rw [appendTaylorStages_initial (by decide)]
  exact CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0002.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 100).coefficient 0 i=endpointData[i.val] := by
  change (appendTaylorStages 50 CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0002.stages CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0003.stages (50+50)).coefficient 0 i=CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0003.endpointData[i.val]
  rw [appendTaylorStages_terminal]
  exact CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0003.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Merge000_0001
