import Lemniscate.PeriodicSinePolynomialNorm

/-! A single estimate accounts for the change of normalization after
Fourier truncation, for both the rotation and the adjoint eigenfunction. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

theorem circle_sine_truncation_rescale_error (f : circleH4Domain T)
    (N : ℕ) (v : Fin N → ℂ) (c : ℂ) :
    circleAngularH4Norm T (f-c • circleSineTrialH4 T N v) ≤
      circleAngularH4Norm T (f-circleSineTrialH4 T N v)+
        ‖1-c‖ * ∑ j : Fin N, ‖v j‖ * ∑ k : Fin 5, (2*(j.val+1:ℕ):ℝ)^k.val := by
  have heq : f-c • circleSineTrialH4 T N v =
      (f-circleSineTrialH4 T N v)+(1-c) • circleSineTrialH4 T N v := by module
  rw [heq]
  apply (circle_angular_h4_norm_add_le T _ _).trans
  rw [circle_angular_h4_norm_smul]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (circle_sine_trial_angular_norm_le T N v) (norm_nonneg _))

end Lemniscate
