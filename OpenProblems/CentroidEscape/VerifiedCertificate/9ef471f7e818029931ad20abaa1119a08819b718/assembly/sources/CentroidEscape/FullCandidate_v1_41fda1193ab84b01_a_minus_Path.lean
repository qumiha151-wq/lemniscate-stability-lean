import CentroidEscape.FullCandidate_v1_41fda1193ab84b01_a_minus_Merge003_0000

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Path
open CentroidEscape CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem first_input_contains : ∀ i : Fin 7,
    |rationalShootingInitial (candidateParameter 2) i-
      (CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Merge003_0000.inputData[i.val].toRational CandidateEndpointChecks.mesh).center|≤
      (CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Merge003_0000.inputData[i.val].toRational CandidateEndpointChecks.mesh).radius := by decide +kernel
theorem initial_contains : ∀ i : Fin 7,
    |rationalShootingInitial (candidateParameter 2) i-
      (((CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Merge003_0000.stages 0).coefficient 0 i).toRational CandidateEndpointChecks.mesh).center|≤
      (((CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Merge003_0000.stages 0).coefficient 0 i).toRational CandidateEndpointChecks.mesh).radius := by
  intro i
  rw [CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Merge003_0000.initialCoefficient]
  exact first_input_contains i
theorem terminal_matches : CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Merge003_0000.endpointData=CandidateEndpointChecks.endpointVectors 2 := by decide +kernel
theorem terminal_coefficients : ∀ i : Fin 7,
    (CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Merge003_0000.stages 750).coefficient 0 i=(CandidateEndpointChecks.endpointVectors 2)[i.val] := by
  intro i
  rw [CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Merge003_0000.terminalCoefficient,terminal_matches]
noncomputable def path : FiniteShootingPath := finiteShootingPathOfStages CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Merge003_0000.stages
theorem checked : path.check CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) (candidateParameter 2)=true :=
  (candidate_path_of_segment_checked 2 CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Merge003_0000.stages CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Merge003_0000.checked initial_contains terminal_coefficients).1
theorem endpoint_matches : path.endpoint CandidateEndpointChecks.mesh=CandidateEndpointChecks.endpointBall 2 :=
  (candidate_path_of_segment_checked 2 CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Merge003_0000.stages CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Merge003_0000.checked initial_contains terminal_coefficients).2
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Path
