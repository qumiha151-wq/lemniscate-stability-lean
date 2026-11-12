import CentroidEscape.FullCandidate_v1_41fda1193ab84b01_b_minus_Merge000_0006
import CentroidEscape.FullCandidate_v1_41fda1193ab84b01_b_minus_Input0014

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge001_0003
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem glue : CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0006.endpointData=CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0014.inputData := by decide +kernel
theorem boundary : ∀ i : Fin 7,
    (CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0006.stages 100).coefficient 0 i=(CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0014.stages 0).coefficient 0 i := by
  intro i
  rw [CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0006.terminalCoefficient,CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0014.initialCoefficient,glue]
noncomputable def inputData : Vector FixedBall 7 := CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0006.inputData
noncomputable def endpointData : Vector FixedBall 7 := CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0014.endpointData
noncomputable def stages : ℕ → FixedTaylorState := appendTaylorStages 100 CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0006.stages CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0014.stages
theorem checked : Order60SegmentValid CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) 150 stages :=
  Order60SegmentValid.append CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0006.checked CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0014.checked boundary
theorem initialCoefficient (i : Fin 7) : (stages 0).coefficient 0 i=inputData[i.val] := by
  change (appendTaylorStages 100 CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0006.stages CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0014.stages 0).coefficient 0 i=CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0006.inputData[i.val]
  rw [appendTaylorStages_initial (by decide)]
  exact CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0006.initialCoefficient i
theorem terminalCoefficient (i : Fin 7) : (stages 150).coefficient 0 i=endpointData[i.val] := by
  change (appendTaylorStages 100 CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge000_0006.stages CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0014.stages (100+50)).coefficient 0 i=CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0014.endpointData[i.val]
  rw [appendTaylorStages_terminal]
  exact CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Input0014.terminalCoefficient i
attribute [irreducible] stages
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Merge001_0003
