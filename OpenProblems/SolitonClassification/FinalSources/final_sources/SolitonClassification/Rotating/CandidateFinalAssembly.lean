module

public import SolitonClassification.Rotating.CandidateRootBudget
public import SolitonClassification.Rotating.RotatingClosedProfileNonconstant
public import SolitonClassification.Rotating.RotatingNormalEvolution

@[expose] public section

/-! Final conditional assembly from the five remaining certificate obligations
to actual closed geometry and its pure-normal elastic evolution. There is no
additional root-existence, periodicity, smoothness or tube hypothesis. -/
namespace SolitonClassification.Rotating.CandidateFinalAssembly
noncomputable section
open Set Metric MeasureTheory CandidateRootBudget NormalEvolution
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

theorem two_sided_tube_of_parameter_ball
    (hplus : FlowTubeNeighborhood 1 (by norm_num) horizon Candidate.initial tubeRadius)
    (hminus : FlowTubeNeighborhood (-1) (by norm_num) horizon Candidate.initial tubeRadius)
    {c : Parameters} (hc : c∈closedBall candidateParameterCenter radius) :
    ∀s∈Icc (-c 2) (c 2),rotatingTrajectory (shootingInitial CandidateInputs.phaseReal c) s∈outerTube := by
  have hd:=parameter_domain hc
  have ha:=initial_set_inside_quarter_tube hd.2
  have hR : 0<tubeRadius := by have hr:=radius_pos; dsimp [tubeRadius]; positivity
  have ha' : shootingInitial CandidateInputs.phaseReal c∈ball Candidate.initial tubeRadius := by
    change dist _ _<tubeRadius
    have hh:=mem_ball.mp ha
    linarith
  apply rotatingTrajectory_two_sided_tube
  · intro t ht
    exact hplus _ ha' t ⟨ht.1,ht.2.trans hd.1.2.le⟩
  · intro t ht
    exact hminus _ ha' t ⟨ht.1,ht.2.trans hd.1.2.le⟩

/-- A concrete geometric/PDE conclusion. The rotation statement means the
specified rotational normal-velocity term is nonzero somewhere; the period
114*c2 is a proved closing period, with no claim that it is minimal. -/
structure GeometricConclusion (c : Parameters) (X Y : ℝ → ℝ → ℝ) : Prop where
  parameter_mem : c∈closedBall candidateParameterCenter radius
  shooting_zero : actualShootingMap CandidateInputs.phaseReal c=0
  unique_in_ball : ∀c'∈closedBall candidateParameterCenter radius,
    actualShootingMap CandidateInputs.phaseReal c'=0 → c'=c
  parameter_signs : 2<c 0 ∧ 0<c 4 ∧ 0<c 2
  closed_profile : IsClosedRotatingProfile (shootingInitial CandidateInputs.phaseReal c) (114*c 2)
  nonconstant_curvature : ¬∃k₀ : ℝ,∀s,rotatingK (shootingInitial CandidateInputs.phaseReal c) s=k₀
  nonzero_rotation : ∃s,c 4*(
    rotatingX (shootingInitial CandidateInputs.phaseReal c) s*
      deriv (rotatingX (shootingInitial CandidateInputs.phaseReal c)) s+
    rotatingY (shootingInitial CandidateInputs.phaseReal c) s*
      deriv (rotatingY (shootingInitial CandidateInputs.phaseReal c)) s)≠0
  total_curvature : (∫s in 0..(114*c 2),rotatingK (shootingInitial CandidateInputs.phaseReal c) s)=
    (-56:ℝ)*(2*Real.pi)
  pure_normal_evolution : IsPureNormalElasticEvolution (114*c 2) X Y
  initial_curve : ∀s,X 0 s=rotatingX (shootingInitial CandidateInputs.phaseReal c) s ∧
    Y 0 s=rotatingY (shootingInitial CandidateInputs.phaseReal c) s
  length_formula : ∀t,-1/4<t →
    (∫s in 0..(114*c 2),curveSpeed (X t) (Y t) s)=dilationScale t*(114*c 2)

/-- The only five substantive premises are the two actual full-neighborhood
flow/matrix certificates and the three center numerical enclosures. This is
an implication, not an unconditional certification of the numeric candidate. -/
theorem exists_geometry_and_pure_normal_evolution_of_remaining_enclosures
    (plus : ActualFlowMatrixBounds 1 (by norm_num) horizon Candidate.initial tubeRadius initialSet 8000 16000)
    (minus : ActualFlowMatrixBounds (-1) (by norm_num) horizon Candidate.initial tubeRadius initialSet 8000 16000)
    (y : Parameters)
    (hvalue : ‖y-actualShootingMap CandidateInputs.phaseReal candidateParameterCenter‖≤(1:ℝ)/10^27)
    (hjacobian : ‖CandidatePreconditioner.J-
      actualShootingDerivative CandidateInputs.phaseReal candidateParameterCenter‖≤(1:ℝ)/10^5)
    (hresidual : ‖CandidatePreconditioner.B y‖≤(1:ℝ)/10^30) :
    ∃c : Parameters,∃X Y : ℝ → ℝ → ℝ,GeometricConclusion c X Y := by
  obtain ⟨c,hc,hzero,hunique⟩ :=
    exists_unique_zero_of_remaining_enclosures plus minus y hvalue hjacobian hresidual
  have hs:=CandidateInputs.parameter_signs_of_ball (r:=radius) le_rfl hc
  have htube:=two_sided_tube_of_parameter_ball plus.tube minus.tube hc
  have hclosed:=actualShooting_closed_profile CandidateInputs.phaseReal c hs.2.2 hzero htube
  obtain ⟨hnon,hrot⟩ := actualShooting_nonconstant_rotating CandidateInputs.phaseReal c
    hs.2.2 hzero htube hs.1 hs.2.1
  have hturn:=actualShooting_total_curvature CandidateInputs.phaseReal c hs.2.2 hzero htube
  obtain ⟨X,Y,hflow,hinit,hlen⟩ := actualShooting_exists_pure_normal_evolution
    CandidateInputs.phaseReal c hs.2.2 hzero htube
  exact ⟨c,X,Y,⟨hc,hzero,hunique,hs,hclosed,hnon,hrot,hturn,hflow,hinit,fun t _=>hlen t⟩⟩

/-- Explicitly exposes the future-global full-velocity PDE from the assembled
conclusion; no new regularity or evolution assumption is introduced. -/
theorem GeometricConclusion.future_PDE {c : Parameters} {X Y : ℝ → ℝ → ℝ}
    (h : GeometricConclusion c X Y) (t : ℝ) (ht : 0≤t) (s : ℝ) :
    HasDerivAt (fun u=>X u s)
      (-intrinsicElasticForce (X t) (Y t) s*unitNormalX (X t) (Y t) s) t ∧
    HasDerivAt (fun u=>Y u s)
      (-intrinsicElasticForce (X t) (Y t) s*unitNormalY (X t) (Y t) s) t :=
  ⟨h.pure_normal_evolution.evolution_X t (by linarith) s,
    h.pure_normal_evolution.evolution_Y t (by linarith) s⟩

end
end SolitonClassification.Rotating.CandidateFinalAssembly

#print axioms SolitonClassification.Rotating.CandidateFinalAssembly.exists_geometry_and_pure_normal_evolution_of_remaining_enclosures
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name || (`ClosedSimilarity).isPrefixOf name then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Final candidate assembly audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Final conditional geometry/PDE assembly audited: {count} declarations; standard axioms only."
