module

public import SolitonClassification.Rotating.FlowMetricCoordinates

@[expose] public section

/-! Both directions of a moving-reference matrix reset. The inverse reset
uses the old reference inverse, whose norm must also be bounded. This
avoids a Neumann-series estimate while retaining every reset defect. -/
namespace SolitonClassification.Rotating
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem metric_forward_reset_algebra (M N P : FlowEnd) (hu : IsUnit M) :
    Ring.inverse N*P=(Ring.inverse N*M)*(Ring.inverse M*P) := by
  have he : M*(Ring.inverse M*P)=P := by
    rw [←mul_assoc,Ring.mul_inverse_cancel M hu,one_mul]
  simp only [mul_assoc,he]

theorem metric_inverse_reset_algebra (M N Q : FlowEnd) (hu : IsUnit M) :
    Q*N=(Q*M)*(Ring.inverse M*N) := by
  have he : M*(Ring.inverse M*N)=N := by
    rw [←mul_assoc,Ring.mul_inverse_cancel M hu,one_mul]
  simp only [mul_assoc,he]

theorem metric_transition_norm_bound {M N : FlowEnd} {I δ : ℝ}
    (hu : IsUnit N) (hI : 0≤I) (hInv : ‖Ring.inverse N‖≤I) (hjump : ‖M-N‖≤δ) :
    ‖Ring.inverse N*M‖≤1+I*δ := by
  have he : Ring.inverse N*M=1+Ring.inverse N*(M-N) := by
    rw [mul_sub,Ring.inverse_mul_cancel N hu]
    abel
  rw [he]
  have hh := (norm_add_le (1:FlowEnd) (Ring.inverse N*(M-N))).trans
    (add_le_add (le_refl ‖(1:FlowEnd)‖)
      ((norm_mul_le _ _).trans (mul_le_mul hInv hjump (norm_nonneg _) hI)))
  simpa only [norm_one] using hh

theorem metric_forward_reset_bound {M N P : FlowEnd} {I δ : ℝ}
    (hM : IsUnit M) (hN : IsUnit N) (hI : 0≤I)
    (hInv : ‖Ring.inverse N‖≤I) (hjump : ‖M-N‖≤δ) :
    ‖Ring.inverse N*P‖≤(1+I*δ)*‖Ring.inverse M*P‖ := by
  rw [metric_forward_reset_algebra M N P hM]
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (metric_transition_norm_bound hN hI hInv hjump) (norm_nonneg _))

theorem metric_inverse_reset_bound {M N Q : FlowEnd} {I δ : ℝ}
    (hM : IsUnit M) (hI : 0≤I)
    (hInv : ‖Ring.inverse M‖≤I) (hjump : ‖M-N‖≤δ) :
    ‖Q*N‖≤(1+I*δ)*‖Q*M‖ := by
  rw [metric_inverse_reset_algebra M N Q hM]
  have he : ‖N-M‖≤δ := by simpa only [norm_sub_rev] using hjump
  exact (norm_mul_le _ _).trans
    ((mul_le_mul_of_nonneg_left (metric_transition_norm_bound hM hI hInv he) (norm_nonneg _)).trans_eq (mul_comm _ _))

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating bidirectional matrix-reset audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating bidirectional matrix-reset audit passed for {count} declarations."

end
