module

public import SolitonClassification.Rotating.FlowMetricReset

@[expose] public section

/-! The full reference reset contribution to deviation from identity.
The extra I*delta term is essential; norm growth alone does not supply it. -/
namespace SolitonClassification.Rotating
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem metric_transition_deviation_bound {M N : FlowEnd} {I δ : ℝ}
    (hN : IsUnit N) (hI : 0≤I) (hInv : ‖Ring.inverse N‖≤I) (hjump : ‖M-N‖≤δ) :
    ‖Ring.inverse N*M-1‖≤I*δ := by
  have he : Ring.inverse N*M-1=Ring.inverse N*(M-N) := by
    rw [mul_sub,Ring.inverse_mul_cancel N hN]
  rw [he]
  exact (norm_mul_le _ _).trans (mul_le_mul hInv hjump (norm_nonneg _) hI)

theorem metric_forward_deviation_reset_bound {M N P : FlowEnd} {I δ : ℝ}
    (hM : IsUnit M) (hN : IsUnit N) (hI : 0≤I)
    (hInv : ‖Ring.inverse N‖≤I) (hjump : ‖M-N‖≤δ) :
    ‖Ring.inverse N*P-1‖+1≤(1+I*δ)*(‖Ring.inverse M*P-1‖+1) := by
  have he : Ring.inverse N*P-1=
      (Ring.inverse N*M)*(Ring.inverse M*P-1)+(Ring.inverse N*M-1) := by
    rw [metric_forward_reset_algebra M N P hM,mul_sub,mul_one]
    abel
  have hn := metric_transition_norm_bound hN hI hInv hjump
  have hd := metric_transition_deviation_bound hN hI hInv hjump
  have hb := (norm_add_le ((Ring.inverse N*M)*(Ring.inverse M*P-1)) (Ring.inverse N*M-1)).trans
    (add_le_add ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))) hd)
  rw [←he] at hb
  nlinarith

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating actual matrix reset-deviation audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating actual matrix reset-deviation audit passed for {count} declarations."
