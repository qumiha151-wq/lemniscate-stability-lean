import Lemniscate.PeriodicSineAdjointTrial

/-! The finite sine trial and all its scalar multiples belong to the
even-frequency sine subspace. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

theorem circle_sine_trial_sector (N : ℕ) (v : Fin N → ℂ) :
    InCircleEvenSineSector T (circleSineTrialH4 T N v : CircleL2 T) := by
  have hc (n : ℤ) : fourierCoeff (circleSineTrialH4 T N v : CircleL2 T) n =
      ∑ j : Fin N, v j*fourierCoeff (circleEvenSineMode T j.val) n := by
    rw [← fourierBasis_repr,HilbertBasis.repr_apply_apply]
    simp only [circleSineTrialH4,Submodule.coe_sum,Submodule.coe_smul_of_tower]
    change inner ℂ (fourierBasis (T := T) n)
      (∑ j : Fin N, v j • circleEvenSineMode T j.val) = _
    simp only [inner_sum,inner_smul_right,← HilbertBasis.repr_apply_apply,fourierBasis_repr]
  constructor
  · intro n
    rw [hc,hc]
    simp only [circle_even_sine_mode_coeff_neg,mul_neg,Finset.sum_neg_distrib]
  · intro n
    rw [hc]
    simp only [circle_even_sine_mode_coeff_odd,mul_zero,Finset.sum_const_zero]

end Lemniscate
