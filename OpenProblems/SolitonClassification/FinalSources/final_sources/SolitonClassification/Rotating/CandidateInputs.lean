module

public import SolitonClassification.Rotating.ShootingVariation
public import SolitonClassification.Rotating.RotatingGridHorizonCandidate

@[expose] public section

/-! Exact candidate phase, signs and initial-state domain. The actual-root
interface uses one quarter of the tube radius: choose an open radius8r
tube for the closed radiusr initial set. No tube certificate is assumed. -/
namespace SolitonClassification.Rotating.CandidateInputs
noncomputable section
open Set Metric
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

def phaseReal : Fin 2 → ℝ := fun i => (Candidate.phase i:ℝ)

theorem phase_checked : |Candidate.phase 0|≤1 ∧ |Candidate.phase 1|≤1 := by
  decide +kernel

theorem phase_bounds : |phaseReal 0|≤1 ∧ |phaseReal 1|≤1 := by
  constructor
  · have h:=(Rat.cast_le (K:=ℝ)).mpr phase_checked.1
    simpa only [Rat.cast_abs,Rat.cast_one,phaseReal] using h
  · have h:=(Rat.cast_le (K:=ℝ)).mpr phase_checked.2
    simpa only [Rat.cast_abs,Rat.cast_one,phaseReal] using h

theorem initial_state_eq : shootingInitial phaseReal candidateParameterCenter=Candidate.initial := by
  ext i
  fin_cases i <;> simp [shootingInitial_apply,phaseReal,candidateParameterCenter,
    Candidate.initial,Candidate.rawInitial]

theorem initial_operator_norm : ‖shootingInitial phaseReal‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  simpa only [one_mul] using shootingInitial_norm_bound phaseReal phase_bounds.1 phase_bounds.2 v

theorem endpoint_input_norm : ‖forwardEndpointInput phaseReal‖≤1 :=
  forwardEndpointInput_norm phaseReal phase_bounds.1 phase_bounds.2

theorem initial_error_of_parameter_ball {c : Parameters} {r : ℝ}
    (hc : c∈closedBall candidateParameterCenter r) :
    ‖shootingInitial phaseReal c-Candidate.initial‖≤r := by
  calc
    _ = ‖shootingInitial phaseReal (c-candidateParameterCenter)‖ := by
      rw [map_sub,initial_state_eq]
    _ ≤ ‖c-candidateParameterCenter‖ :=
      shootingInitial_norm_bound phaseReal phase_bounds.1 phase_bounds.2 _
    _ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hc

theorem initial_mem_closedBall {c : Parameters} {r : ℝ}
    (hc : c∈closedBall candidateParameterCenter r) :
    shootingInitial phaseReal c∈closedBall Candidate.initial r := by
  simpa only [mem_closedBall,dist_eq_norm] using initial_error_of_parameter_ball hc

theorem initial_set_subset_quarter_tube {r : ℝ} (hr : 0<r) :
    closedBall Candidate.initial r⊆ball Candidate.initial ((8*r)/4) := by
  intro x hx
  change dist x Candidate.initial < (8*r)/4
  have h:=mem_closedBall.mp hx
  linarith

theorem parameter_signs_checked :
    (2:ℚ)<Candidate.parameters 0-candidateWideTimeRadius ∧
      0<Candidate.parameters 4-candidateWideTimeRadius ∧
      0<Candidate.parameters 2-candidateWideTimeRadius := by
  decide +kernel

theorem parameter_signs_of_ball {c : Parameters} {r : ℝ}
    (hrmax : r≤(candidateWideTimeRadius:ℝ))
    (hc : c∈closedBall candidateParameterCenter r) : 2<c 0 ∧ 0<c 4 ∧ 0<c 2 := by
  have hn : ‖c-candidateParameterCenter‖≤r := by
    simpa only [mem_closedBall,dist_eq_norm] using hc
  have hb (i : Fin 5) : (Candidate.parameters i:ℝ)-r≤c i := by
    have h : |c i-(Candidate.parameters i:ℝ)|≤r := by
      simpa only [Pi.sub_apply,Real.norm_eq_abs,candidateParameterCenter] using
        (norm_le_pi_norm (c-candidateParameterCenter) i).trans hn
    linarith [(abs_le.mp h).1]
  have h0:=(Rat.cast_lt (K:=ℝ)).mpr parameter_signs_checked.1
  have h4:=(Rat.cast_lt (K:=ℝ)).mpr parameter_signs_checked.2.1
  have h2:=(Rat.cast_lt (K:=ℝ)).mpr parameter_signs_checked.2.2
  push_cast at h0 h4 h2
  exact ⟨by linarith [hb 0],by linarith [hb 4],by linarith [hb 2]⟩

end
end SolitonClassification.Rotating.CandidateInputs

#print axioms SolitonClassification.Rotating.CandidateInputs.initial_state_eq
#print axioms SolitonClassification.Rotating.CandidateInputs.initial_set_subset_quarter_tube
#print axioms SolitonClassification.Rotating.CandidateInputs.parameter_signs_of_ball
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Concrete candidate input/domain audit passed: {count} declarations; standard axioms only."
