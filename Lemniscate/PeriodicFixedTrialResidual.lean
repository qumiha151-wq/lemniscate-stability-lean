import Lemniscate.AdjointResidualTail
import Lemniscate.PeriodicSineAdjointTrial

/-! The residual estimate for the fixed rational trial is an estimate for the
actual adjoint differential operator, including every Fourier coefficient. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

theorem raw_trial_residual_square_sum :
    (∑' k : ℕ, (rawTrialResidual (k+1))^2) < (2:ℝ)/10^30 := by
  have ht := raw_trial_residual_tail_bound
  have hs : Summable (fun k : ℕ => (rawTrialResidual (k+1))^2) := by
    apply (summable_nat_add_iff 40).mp
    simpa only [Nat.add_assoc,Nat.reduceAdd] using ht.1
  have hh : (∑ j : Fin 40, (rawTrialResidual (j.val+1))^2) ≤
      ∑ j : Fin 40, (rawTrialResidualBound j:ℝ)^2 := by
    apply Finset.sum_le_sum
    intro j _
    have h := pow_le_pow_left₀ (abs_nonneg _) (raw_trial_residual_head_bound j) 2
    simpa only [sq_abs,rawTrialResidual] using h
  rw [← hs.sum_add_tsum_nat_add 40,← Fin.sum_univ_eq_sum_range]
  simp only [Nat.add_assoc,Nat.reduceAdd]
  apply (add_le_add hh ht.2).trans_lt
  have hnum : (((∑ j : Fin 40, (rawTrialResidualBound j)^2)+rawTrialTailBound:ℚ):ℝ) <
      ((2/10^30:ℚ):ℝ) := Rat.cast_lt.mpr raw_trial_residual_square_comparison
  push_cast at hnum
  exact hnum

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleAdjointTrial : circleH4Domain T :=
  circleSineTrialH4 T 18 (fun j => (adjointTrialCoefficient j:ℂ))

theorem circle_adjoint_trial_residual_sq (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (ho : ∀ n : ℤ, fourierCoeff h (2*n+1) = 0)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) :
    ‖circleH4FormalAdjoint T h h₁ (circleAdjointTrial T)‖^2 < (2:ℝ)/10^30 := by
  rw [circleAdjointTrial,circle_adjoint_sine_trial_norm_sq T h h₁ h₂ hh hh₁
    hreal h₁real h₂real hs ho]
  have hcoeff (k : ℕ) :
      (∑ j : Fin 18, (adjointTrialCoefficient j:ℂ)*
        (conj (circleBlochFourierEntry T h 0 (2*((j.val+1:ℕ):ℤ)) (2*((k+1:ℕ):ℤ)))-
         conj (circleBlochFourierEntry T h 0 (-(2*((j.val+1:ℕ):ℤ))) (2*((k+1:ℕ):ℤ))))) =
        (rawTrialResidual (k+1):ℂ) := by
    simp only [rawTrialResidual,
      Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_ratCast]
    apply Finset.sum_congr rfl
    intro j _
    rw [← map_sub,circle_sine_operator_entry T h thetaParameter nome hs hc hr
      (j.val+1) (k+1) (by omega) (by omega),Complex.conj_ofReal]
    ring
  simpa only [hcoeff,Complex.norm_real,Real.norm_eq_abs,sq_abs] using
    raw_trial_residual_square_sum

end Lemniscate
