import CentroidEscape.FiniteTaylorBlock
import CentroidEscape.FivePathCertificate
import CentroidEscape.CandidateEndpointChecks

/-! Typed assembly interface for five completely checked750-step paths.
This generic module does not assert that the concrete paths exist yet. -/
namespace CentroidEscape.MetricStability
noncomputable section
open Set Real Filter
open scoped Topology ContDiff NNReal
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

def candidateParameter (k : Fin 5) : RationalVector3 :=
  ![CandidateEndpointChecks.parameters,
    CandidateEndpointChecks.parameters+(1/10^25:ℚ) • Pi.single (spatialParameterIndex 0) 1,
    CandidateEndpointChecks.parameters-(1/10^25:ℚ) • Pi.single (spatialParameterIndex 0) 1,
    CandidateEndpointChecks.parameters+(1/10^25:ℚ) • Pi.single (spatialParameterIndex 1) 1,
    CandidateEndpointChecks.parameters-(1/10^25:ℚ) • Pi.single (spatialParameterIndex 1) 1] k

def candidateCertificate (paths : Fin 5 → FiniteShootingPath) : FivePathCertificateData :=
  ⟨CandidateEndpointChecks.mesh,CandidateEndpointChecks.parameters,paths 0,
    (fun i=>paths (![1,3] i)),(fun i=>paths (![2,4] i)),CandidateEndpointChecks.preconditioner⟩

theorem candidate_certificate_checked (paths : Fin 5 → FiniteShootingPath)
    (hpaths : ∀ k, (paths k).check CandidateEndpointChecks.mesh
      (CandidateEndpointChecks.parameters 2/750) (candidateParameter k)=true)
    (hend : ∀ k, (paths k).endpoint CandidateEndpointChecks.mesh=CandidateEndpointChecks.endpointBall k) :
    (candidateCertificate paths).check=true := by
  let d := candidateCertificate paths
  have hc : d.centerBall=CandidateEndpointChecks.endpointBall 0 := hend 0
  have hf : d.fieldBall=CandidateEndpointChecks.timeBalls := by
    change evaluateWeightedField CandidateEndpointChecks.mesh d.centerBall=CandidateEndpointChecks.timeBalls
    rw [hc]
    rfl
  have hco : d.centerOutput=CandidateEndpointChecks.centerOutput := by
    change projectedRationalCenter d.centerBall=CandidateEndpointChecks.centerOutput
    rw [hc]
    rfl
  have hp : d.plusOutput=CandidateEndpointChecks.plusOutput := by
    funext i
    change projectedRationalCenter ((paths (![1,3] i)).endpoint CandidateEndpointChecks.mesh)=_
    rw [hend]
    rfl
  have hm : d.minusOutput=CandidateEndpointChecks.minusOutput := by
    funext i
    change projectedRationalCenter ((paths (![2,4] i)).endpoint CandidateEndpointChecks.mesh)=_
    rw [hend]
    rfl
  have hj : d.jacobian=CandidateEndpointChecks.proposedJacobian := by
    change fivePathRationalJacobian (1/10^25) d.plusOutput d.minusOutput
      (projectedRationalCenter d.fieldBall)=_
    rw [hp,hm,hf]
    rfl
  apply decide_eq_true
  change d.Valid
  refine ⟨by change 0<CandidateEndpointChecks.mesh; decide +kernel,CandidateEndpointChecks.parameter_bounds.1,
    CandidateEndpointChecks.parameter_bounds.2,hpaths 0,?_,?_,?_,
    CandidateEndpointChecks.preconditioner_bound,?_,?_,?_⟩
  · intro i
    fin_cases i
    · exact hpaths 1
    · exact hpaths 3
  · intro i
    fin_cases i
    · exact hpaths 2
    · exact hpaths 4
  · rw [hf]
    exact CandidateEndpointChecks.time_column_width
  · rw [hj]
    exact CandidateEndpointChecks.inverse_defect
  · rw [hco]
    exact CandidateEndpointChecks.center_residual
  · rw [hc]
    exact CandidateEndpointChecks.center_moment

theorem candidate_path_of_segment_checked (k : Fin 5) (st : ℕ → FixedTaylorState)
    (hv : Order60SegmentValid CandidateEndpointChecks.mesh
      (CandidateEndpointChecks.parameters 2/750) 750 st)
    (hi : ∀ i : Fin 7,
      |rationalShootingInitial (candidateParameter k) i-
        (((st 0).coefficient 0 i).toRational CandidateEndpointChecks.mesh).center|≤
        (((st 0).coefficient 0 i).toRational CandidateEndpointChecks.mesh).radius)
    (ht : ∀ i : Fin 7, (st 750).coefficient 0 i=(CandidateEndpointChecks.endpointVectors k)[i.val]) :
    (finiteShootingPathOfStages st).check CandidateEndpointChecks.mesh
      (CandidateEndpointChecks.parameters 2/750) (candidateParameter k)=true ∧
    (finiteShootingPathOfStages st).endpoint CandidateEndpointChecks.mesh=CandidateEndpointChecks.endpointBall k := by
  have he : order60EndpointBalls CandidateEndpointChecks.mesh 750 st=CandidateEndpointChecks.endpointBall k := by
    funext i
    change (((st 750).coefficient 0 i).toRational CandidateEndpointChecks.mesh).inflate (1/10^43)=_
    rw [ht]
    rfl
  have hr : checkProjectedRadius (order60EndpointBalls CandidateEndpointChecks.mesh 750 st) (1/10^40)=true := by
    rw [he]
    exact CandidateEndpointChecks.endpoint_widths k
  refine ⟨finiteShootingPathOfStages_checked hv hi hr,?_⟩
  funext i
  change ((((finiteShootingPathOfStages st).stage 750).coefficient 0 i).toRational CandidateEndpointChecks.mesh).inflate
    (1/10^43)=CandidateEndpointChecks.endpointBall k i
  rw [finiteShootingPathOfStages_stage (by omega),ht]
  rfl

theorem candidate_certificate_escape (paths : Fin 5 → FiniteShootingPath)
    (hpaths : ∀ k, (paths k).check CandidateEndpointChecks.mesh
      (CandidateEndpointChecks.parameters 2/750) (candidateParameter k)=true)
    (hend : ∀ k, (paths k).endpoint CandidateEndpointChecks.mesh=CandidateEndpointChecks.endpointBall k) :
    ∃ L : ℝ, 0<L ∧ ∃ γ : ℝ → ℝ → Plane,
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ=>γ q.1 q.2) {q | -1/4<q.1} ∧
      (∀t, Function.Periodic (γ t) (2*L) ∧ ContDiff ℝ ∞ (γ t)) ∧
      (∀t, 0≤t → ∀s, 0<‖deriv (γ t) s‖) ∧
      (∀t, 0≤t → ∀s, HasDerivAt (fun r=>γ r s)
        ((-curveElasticForce (γ t) s) • curveUnitNormal (γ t) s) t) ∧
      Tendsto (fun t=>curveCentroidX (2*L) (γ t)) atTop atTop :=
  checked_fivePathCertificate_yields_smooth_classical_FEF_escape
    (candidateCertificate paths) (candidate_certificate_checked paths hpaths hend)

end
end CentroidEscape.MetricStability

#print axioms CentroidEscape.MetricStability.candidate_certificate_escape
