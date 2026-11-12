import CentroidEscape.FullCandidate_v1_41fda1193ab84b01_a_minus_Input0012
import CentroidEscape.FullCandidate_v1_41fda1193ab84b01_a_minus_Input0013

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Merge000_0006
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem glue : CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0012.endpointData=CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0013.inputData := by decide +kernel
theorem boundary : ∀ i : Fin 7,
    (CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0012.stages 50).coefficient 0 i=(CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0013.stages 0).coefficient 0 i := by
  intro i
  rw [CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0012.terminalCoefficient,CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0013.initialCoefficient,glue]
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0012.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0013.endpointData
noncomputable def stages : ℕ → FixedTaylorState := appendTaylorStages 50 CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0012.stages CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0013.stages
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 100 stages :=
  Order60SegmentValid.append CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0012.checked CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0013.checked boundary
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change (appendTaylorStages 50 CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0012.stages CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0013.stages 0).coefficient 0 i=CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0012.inputData[i.val]
  rw [appendTaylorStages_initial (by decide)]
  exact CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0012.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 100).coefficient 0 i=endpointData[i.val] := by
  change (appendTaylorStages 50 CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0012.stages CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0013.stages (50+50)).coefficient 0 i=CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0013.endpointData[i.val]
  rw [appendTaylorStages_terminal]
  exact CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Input0013.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Merge000_0006
