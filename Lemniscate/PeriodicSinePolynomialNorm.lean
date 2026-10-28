import Lemniscate.PeriodicSineDerivativeNorm
import Lemniscate.PeriodicAngularH4Norm

/-! The angular Sobolev norm of a sine polynomial is bounded by exactly
the weighted coefficient sum L4 used in the manuscript. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

theorem circle_sine_h4_angular_norm (n : ℕ) :
    circleAngularH4Norm T (circleSineH4 T n) =
      ∑ k : Fin 5, (2*(n+1:ℕ):ℝ)^k.val := by
  have h1 := circle_sine_h4_derivative_norm T ⟨0,by decide⟩ n
  have h2 := circle_sine_h4_derivative_norm T ⟨1,by decide⟩ n
  have h3 := circle_sine_h4_derivative_norm T ⟨2,by decide⟩ n
  have h4 := circle_sine_h4_derivative_norm T ⟨3,by decide⟩ n
  change ‖(circleH4Jet T (circleSineH4 T n)).first‖ =
    (2*Real.pi/T*(2*(n+1:ℕ):ℝ))^1 at h1
  change ‖(circleH4Jet T (circleSineH4 T n)).second‖ =
    (2*Real.pi/T*(2*(n+1:ℕ):ℝ))^2 at h2
  change ‖(circleH4Jet T (circleSineH4 T n)).third‖ =
    (2*Real.pi/T*(2*(n+1:ℕ):ℝ))^3 at h3
  change ‖(circleH4Jet T (circleSineH4 T n)).fourth‖ =
    (2*Real.pi/T*(2*(n+1:ℕ):ℝ))^4 at h4
  have h0 : ‖(circleSineH4 T n : CircleL2 T)‖ = 1 :=
    (circle_even_sine_orthonormal T).norm_eq_one n
  have hκ : 2*Real.pi/T ≠ 0 := ne_of_gt (div_pos (by positivity) (Fact.out : 0 < T))
  simp only [circleAngularH4Norm,h0,h1,h2,h3,h4]
  norm_num [Fin.sum_univ_succ]
  field_simp [hκ,ne_of_gt (Fact.out : 0 < T),Real.pi_ne_zero]
  <;> ring

private theorem angular_norm_sum_le {ι : Type*} (s : Finset ι) (f : ι → circleH4Domain T) :
    circleAngularH4Norm T (∑ i ∈ s, f i) ≤ ∑ i ∈ s, circleAngularH4Norm T (f i) := by
  classical
  have hz : circleAngularH4Norm T 0 = 0 := by
    simpa only [zero_smul,norm_zero,zero_mul] using
      circle_angular_h4_norm_smul T 0 (0 : circleH4Domain T)
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,hz,le_refl]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (circle_angular_h4_norm_add_le T _ _).trans (add_le_add le_rfl ih)

theorem circle_sine_trial_angular_norm_le (N : ℕ) (v : Fin N → ℂ) :
    circleAngularH4Norm T (circleSineTrialH4 T N v) ≤
      ∑ j : Fin N, ‖v j‖ * ∑ k : Fin 5, (2*(j.val+1:ℕ):ℝ)^k.val := by
  exact (angular_norm_sum_le T Finset.univ (fun j : Fin N => v j • circleSineH4 T j.val)).trans_eq
    (by simp only [circle_angular_h4_norm_smul,circle_sine_h4_angular_norm])

end Lemniscate
