module

public import SolitonClassification.Rotating.RotatingGridHorizon
public import SolitonClassification.Rotating.CandidateInitial

@[expose] public section

/-! Exact time-margin arithmetic for the stored candidate center and
radii 1e-32 and 1e-24. No reference trajectory or shooting root is asserted. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set UniversalMajorant
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def candidateTimeRadius : ℚ := 1/10^32
def candidateWideTimeRadius : ℚ := 1/10^24
def candidateParameterCenter : Parameters := fun i => (Candidate.parameters i : ℝ)
def candidateExtendedHorizon : ℝ := (Candidate.parameters 2:ℝ)+2*(candidateTimeRadius:ℝ)
def candidateWideExtendedHorizon : ℝ := (Candidate.parameters 2:ℝ)+2*(candidateWideTimeRadius:ℝ)

theorem candidate_time_extension_checked :
    0<candidateTimeRadius ∧ candidateTimeRadius<Candidate.parameters 2 ∧
      Candidate.step+2*candidateTimeRadius<Candidate.stepCap ∧
      Candidate.parameters 2+2*candidateTimeRadius<32 := by
  decide +kernel

theorem candidate_time_radius_pos : (0:ℝ)<(candidateTimeRadius:ℝ) :=
  Rat.cast_pos.mpr candidate_time_extension_checked.1

theorem candidate_last_step_extension_cap :
    (Candidate.step:ℝ)+2*(candidateTimeRadius:ℝ)≤(universalStepCap:ℝ) := by
  have h := (Rat.cast_lt (K:=ℝ)).mpr candidate_time_extension_checked.2.2.1
  push_cast at h
  exact h.le

theorem candidateExtendedHorizon_eq : candidateExtendedHorizon=
    (4000:ℝ)*(Candidate.step:ℝ)+2*(candidateTimeRadius:ℝ) := by
  simp only [candidateExtendedHorizon,Candidate.step,Rat.cast_div,Rat.cast_ofNat]
  ring

theorem candidateExtendedHorizon_lt_32 : candidateExtendedHorizon<32 := by
  have h := (Rat.cast_lt (K:=ℝ)).mpr candidate_time_extension_checked.2.2.2
  push_cast at h
  exact h

theorem candidate_parameter_time_domain {c : Parameters}
    (hc : c∈Metric.closedBall candidateParameterCenter (candidateTimeRadius:ℝ)) :
    c 2∈Ioo 0 candidateExtendedHorizon := by
  apply shooting_length_in_extended_horizon candidate_time_radius_pos _ hc
  exact (Rat.cast_lt (K:=ℝ)).mpr candidate_time_extension_checked.2.1

theorem candidate_signed_grid_local_cap (σ : ℝ) (hσ : |σ|≤1)
    {j : ℕ} (hj : j<4000) {t : ℝ}
    (ht : t∈Icc (extendedGridTime 4000 (Candidate.step:ℝ) (candidateTimeRadius:ℝ) j)
      (extendedGridTime 4000 (Candidate.step:ℝ) (candidateTimeRadius:ℝ) (j+1))) :
    |σ*(t-(j:ℝ)*(Candidate.step:ℝ))|≤(universalStepCap:ℝ) :=
  extendedGridTime_signed_local_cap σ hσ hj candidate_time_radius_pos.le candidate_last_step_extension_cap ht

theorem candidate_center_endpoint_preserved :
    (Candidate.parameters 2:ℝ)∈Icc
      (extendedGridTime 4000 (Candidate.step:ℝ) (candidateTimeRadius:ℝ) 3999)
      (extendedGridTime 4000 (Candidate.step:ℝ) (candidateTimeRadius:ℝ) 4000) := by
  have h := center_endpoint_in_extended_last_segment (N:=4000) (by norm_num)
    (Rat.cast_pos.mpr Candidate.positive_step).le candidate_time_radius_pos.le
  have he : (4000:ℝ)*(Candidate.step:ℝ)=(Candidate.parameters 2:ℝ) := by
    simp only [Candidate.step,Rat.cast_div,Rat.cast_ofNat]
    ring
  norm_num only [Nat.cast_ofNat,Nat.reduceSub] at h
  rw [he] at h
  exact h

theorem candidate_wide_time_extension_checked :
    0<candidateWideTimeRadius ∧ candidateWideTimeRadius<Candidate.parameters 2 ∧
      Candidate.step+2*candidateWideTimeRadius<Candidate.stepCap ∧
      Candidate.parameters 2+2*candidateWideTimeRadius<32 := by
  decide +kernel

theorem candidate_wide_time_radius_pos : (0:ℝ)<(candidateWideTimeRadius:ℝ) :=
  Rat.cast_pos.mpr candidate_wide_time_extension_checked.1

/-- Uniform rational time slack for ANY real radius at most 1e-24.
Actual bootstrap budgets must still be established for the chosen radius. -/
theorem candidate_extension_for_radius {r : ℝ} (hr : r≤(candidateWideTimeRadius:ℝ)) :
    (Candidate.step:ℝ)+2*r≤(universalStepCap:ℝ) ∧
      r<(Candidate.parameters 2:ℝ) ∧ (Candidate.parameters 2:ℝ)+2*r<32 := by
  have hc := (Rat.cast_lt (K:=ℝ)).mpr candidate_wide_time_extension_checked.2.2.1
  have hl := (Rat.cast_lt (K:=ℝ)).mpr candidate_wide_time_extension_checked.2.1
  have ht := (Rat.cast_lt (K:=ℝ)).mpr candidate_wide_time_extension_checked.2.2.2
  push_cast at hc ht
  have hcap : (Candidate.step:ℝ)+2*(candidateWideTimeRadius:ℝ)<(universalStepCap:ℝ) := hc
  exact ⟨by linarith,by linarith,by linarith⟩

theorem candidate_parameter_time_domain_of_radius {c : Parameters} {r : ℝ}
    (hr : 0<r) (hrmax : r≤(candidateWideTimeRadius:ℝ))
    (hc : c∈Metric.closedBall candidateParameterCenter r) :
    c 2∈Ioo 0 ((Candidate.parameters 2:ℝ)+2*r) :=
  shooting_length_in_extended_horizon hr (candidate_extension_for_radius hrmax).2.1 hc

theorem candidate_wide_parameter_time_domain {c : Parameters}
    (hc : c∈Metric.closedBall candidateParameterCenter (candidateWideTimeRadius:ℝ)) :
    c 2∈Ioo 0 candidateWideExtendedHorizon :=
  candidate_parameter_time_domain_of_radius candidate_wide_time_radius_pos le_rfl hc

theorem candidate_signed_grid_local_cap_of_radius (σ : ℝ) (hσ : |σ|≤1)
    {r : ℝ} (hr : 0≤r) (hrmax : r≤(candidateWideTimeRadius:ℝ))
    {j : ℕ} (hj : j<4000) {t : ℝ}
    (ht : t∈Icc (extendedGridTime 4000 (Candidate.step:ℝ) r j)
      (extendedGridTime 4000 (Candidate.step:ℝ) r (j+1))) :
    |σ*(t-(j:ℝ)*(Candidate.step:ℝ))|≤(universalStepCap:ℝ) :=
  extendedGridTime_signed_local_cap σ hσ hj hr (candidate_extension_for_radius hrmax).1 ht

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating candidate time-neighborhood audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating candidate time-neighborhood audit passed for {count} declarations."
