import SolitonClassification.Rotating.FullCandidate
import SolitonClassification.CandidatePitchBranch

/-! Final application for the Linux build containing both actual 4000-step
grids. This file is outside the normal project entry point. -/
noncomputable section
namespace SolitonClassification.Rotating.FullPitchAccumulation

theorem exists_dense_positive_closed_rotating_pitches :
    ∃ lo hi : ℝ, 0<lo ∧ lo<hi ∧
      ∀ x y : ℝ, lo≤x → x<y → y≤hi →
        ∃ c : Parameters, ∃ u : ℚ, x<c 4 ∧ c 4<y ∧
          IsClosedRotatingProfile (shootingInitial CandidateInputs.phaseReal c) ((u.den:ℝ)*(2*c 2)) ∧
          ¬∃ k : ℝ, ∀ s, rotatingK (shootingInitial CandidateInputs.phaseReal c) s=k := by
  have h := FullPathFinalInputs.final_inputs_of_two_blocks
    FullGridP.certificate FullGridM.certificate
    FullGridP.state_start FullGridP.matrix_start FullGridM.state_start FullGridM.matrix_start
    FullGridPActual.terminal_state FullGridPActual.terminal_matrix
    FullGridMActual.terminal_state FullGridMActual.terminal_matrix
  exact CandidatePitchBranch.actual_closed_pitch_dense_of_remaining_enclosures
    h.plus h.minus Endpoint4000Finite.value h.value h.jacobian h.residual

end SolitonClassification.Rotating.FullPitchAccumulation

open Lean Elab Command in
run_cmd do
  let n := `SolitonClassification.Rotating.FullPitchAccumulation.exists_dense_positive_closed_rotating_pitches
  for ax in (← collectAxioms n) do
    unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains ax do
      throwError "Dense actual-pitch result depends on {ax}"
  logInfo "Dense actual-pitch theorem passed the standard three-axiom audit."
