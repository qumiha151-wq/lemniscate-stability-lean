import Lemniscate.PeriodicBlochParity

/-! Reflection identifies opposite real Bloch parameters on the same H4
domain. Consequently the nonnegative-parameter estimate suffices. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T : ℝ) [Fact (0 < T)]
set_option maxRecDepth 2000

theorem circle_bloch_reflect (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (α : ℝ) (f : circleH4Domain T) :
    circleBlochOperator T h h₁ h₂ α (circleReflectH4 T f) =
      circleReflect T (circleBlochOperator T h h₁ h₂ (-α) f) := by
  rw [circle_bloch_polynomial,circle_bloch_polynomial]
  simp only [circle_bloch_coefficient_reflect T h h₁ h₂ hh hh₁ hs,
    circle_reflect_add,circle_reflect_smul,Complex.ofReal_neg]
  norm_num only [show ((2:Fin 5):ℕ) = 2 from rfl,
    show ((3:Fin 5):ℕ) = 3 from rfl,show ((4:Fin 5):ℕ) = 4 from rfl,
    Fin.val_zero,Fin.val_one,pow_zero,pow_one,
    one_smul,neg_one_smul]
  module

theorem circle_bloch_reflected_eigenvector (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (α : ℝ) (w : ℂ) (f : circleH4Domain T) (hf : (f:CircleL2 T) ≠ 0)
    (hAf : circleBlochOperator T h h₁ h₂ α f = w • (f:CircleL2 T)) :
    (circleReflectH4 T f:CircleL2 T) ≠ 0 ∧
      circleBlochOperator T h h₁ h₂ (-α) (circleReflectH4 T f) =
        w • (circleReflectH4 T f:CircleL2 T) := by
  constructor
  · intro hz
    have hn := congrArg norm hz
    change ‖circleReflect T (f:CircleL2 T)‖ = ‖(0:CircleL2 T)‖ at hn
    rw [circle_reflect_norm,norm_zero] at hn
    exact hf (norm_eq_zero.mp hn)
  · rw [circle_bloch_reflect T h h₁ h₂ hh hh₁ hs,neg_neg,hAf,circle_reflect_smul]
    rfl

end Lemniscate
