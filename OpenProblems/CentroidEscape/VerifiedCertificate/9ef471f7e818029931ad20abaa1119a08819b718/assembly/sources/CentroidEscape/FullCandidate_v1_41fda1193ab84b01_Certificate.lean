import CentroidEscape.FullCandidate_v1_41fda1193ab84b01_center_Path
import CentroidEscape.FullCandidate_v1_41fda1193ab84b01_a_plus_Path
import CentroidEscape.FullCandidate_v1_41fda1193ab84b01_a_minus_Path
import CentroidEscape.FullCandidate_v1_41fda1193ab84b01_b_plus_Path
import CentroidEscape.FullCandidate_v1_41fda1193ab84b01_b_minus_Path

namespace CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.Certificate
open CentroidEscape CentroidEscape.MetricStability Set Real Filter
open scoped Topology ContDiff NNReal
noncomputable def paths : Fin 5 → FiniteShootingPath := ![CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Path.path,CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Path.path,CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Path.path,CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Path.path,CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Path.path]
theorem paths_checked : ∀ k, (paths k).check CandidateEndpointChecks.mesh
    (CandidateEndpointChecks.parameters 2/750) (candidateParameter k)=true := by
  intro k
  fin_cases k
  · exact CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Path.checked
  · exact CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Path.checked
  · exact CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Path.checked
  · exact CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Path.checked
  · exact CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Path.checked
theorem endpoints_match : ∀ k, (paths k).endpoint CandidateEndpointChecks.mesh=CandidateEndpointChecks.endpointBall k := by
  intro k
  fin_cases k
  · exact CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.center.Path.endpoint_matches
  · exact CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_plus.Path.endpoint_matches
  · exact CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.a_minus.Path.endpoint_matches
  · exact CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_plus.Path.endpoint_matches
  · exact CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.b_minus.Path.endpoint_matches

noncomputable def data : FivePathCertificateData := candidateCertificate paths
theorem checked : data.check=true := candidate_certificate_checked paths paths_checked endpoints_match
theorem smooth_FEF_centroid_escape :
    ∃ L : ℝ, 0<L ∧ ∃ γ : ℝ → ℝ → Plane,
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ=>γ q.1 q.2) {q | -1/4<q.1} ∧
      (∀t, Function.Periodic (γ t) (2*L) ∧ ContDiff ℝ ∞ (γ t)) ∧
      (∀t, 0≤t → ∀s, 0<‖deriv (γ t) s‖) ∧
      (∀t, 0≤t → ∀s, HasDerivAt (fun r=>γ r s)
        ((-curveElasticForce (γ t) s) • curveUnitNormal (γ t) s) t) ∧
      Tendsto (fun t=>curveCentroidX (2*L) (γ t)) atTop atTop :=
  checked_fivePathCertificate_yields_smooth_classical_FEF_escape data checked
end CentroidEscape.FullCertificates.FullCandidate_v1_41fda1193ab84b01.Certificate
