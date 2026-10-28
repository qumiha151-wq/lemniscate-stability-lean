import Lemniscate.PeriodicTruncationRescale

/-! Truncating a finite sine polynomial and changing its normalization.
This controls the omitted three modes of the fixed adjoint trial. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

theorem circle_finite_sine_truncation_error (N M : ℕ) (v : Fin (N+M) → ℂ) (c : ℂ) :
    circleAngularH4Norm T (circleSineTrialH4 T (N+M) v-
      c • circleSineTrialH4 T N (fun j => v (Fin.castAdd M j))) ≤
      (∑ j : Fin M, ‖v (Fin.natAdd N j)‖ *
        ∑ k : Fin 5, (2*(N+j.val+1:ℕ):ℝ)^k.val)+
      ‖1-c‖ * ∑ j : Fin N, ‖v (Fin.castAdd M j)‖ *
        ∑ k : Fin 5, (2*(j.val+1:ℕ):ℝ)^k.val := by
  let w : Fin (N+M) → ℂ := fun j => if j.val < N then 0 else v j
  have hw : circleSineTrialH4 T (N+M) w =
      ∑ j : Fin M, v (Fin.natAdd N j) • circleSineH4 T (N+j.val) := by
    rw [circleSineTrialH4,Fin.sum_univ_add]
    simp only [w,Fin.val_castAdd,Fin.val_natAdd,Fin.isLt,if_true,zero_smul,
      Finset.sum_const_zero,zero_add,show ∀ j : Fin M, ¬N+j.val < N by omega,if_false]
  have hsplit : circleSineTrialH4 T (N+M) v =
      circleSineTrialH4 T N (fun j => v (Fin.castAdd M j))+
      circleSineTrialH4 T (N+M) w := by
    rw [hw,circleSineTrialH4,Fin.sum_univ_add]
    rfl
  have hraw := circle_sine_trial_angular_norm_le T (N+M) w
  rw [Fin.sum_univ_add] at hraw
  simp only [w,Fin.val_castAdd,Fin.val_natAdd,Fin.isLt,if_true,norm_zero,zero_mul,
    Finset.sum_const_zero,zero_add,show ∀ j : Fin M, ¬N+j.val < N by omega,if_false] at hraw
  have h := circle_sine_truncation_rescale_error T (circleSineTrialH4 T (N+M) v)
    N (fun j => v (Fin.castAdd M j)) c
  apply h.trans
  apply add_le_add _ le_rfl
  rw [hsplit,add_sub_cancel_left]
  exact hraw

end Lemniscate
