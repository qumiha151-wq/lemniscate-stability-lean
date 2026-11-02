import Lemniscate.PeriodicBlochResolventFactorization
import Lemniscate.PeriodicBlochParity

/-! Bounded L2 coefficients obtained by composing the actual H4-domain Bloch
polynomial with the principal inverse. This parametrizes the full H4 domain
by an existing Banach space; no new Sobolev norm is introduced. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T : ℝ) [Fact (0 < T)]

noncomputable def circlePrincipalBlochCoefficient (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p) (j : Fin 5) : CircleL2 T →L[ℂ] CircleL2 T :=
  let R := circlePrincipalResolvent T (p^4) (by positivity)
  let R₁ := circlePrincipalFirst T (p^2) (by nlinarith)
  let R₂ := circlePrincipalSecond T (p^2) (by nlinarith)
  let R₃ := circlePrincipalThird T p (by linarith)
  let c := circleFrequencyFactor T 1
  ![((p^4:ℝ):ℂ) • R-1+circleBlochLowerResolvent T h h₁ h₂ 0 p hp,
    c • ((-16:ℂ) • R₃-(90:ℂ) • (circleMultiplyL2 T h).comp R₁-
      (75/2:ℂ) • (circleMultiplyL2 T h₁).comp R),
    c^2 • ((-24:ℂ) • R₂-(45:ℂ) • (circleMultiplyL2 T h).comp R),
    c^3 • ((-16:ℂ) • R₁),c^4 • ((-4:ℂ) • R)] j

private theorem principal_first_second_jets (p : ℝ) (hp : 1 ≤ p) (f : CircleL2 T) :
    circlePrincipalFirst T (p^2) (by nlinarith) f =
      (circleH4Jet T (circlePrincipalResolventH4 T (p^4) (by positivity) f)).first ∧
    circlePrincipalSecond T (p^2) (by nlinarith) f =
      (circleH4Jet T (circlePrincipalResolventH4 T (p^4) (by positivity) f)).second := by
  constructor
  · simpa [circleBlochPrincipalFirst,circleShiftedFirst,circleH4Derivative] using
      circle_bloch_principal_first_eq T 0 p hp f
  · simpa [circleBlochPrincipalSecond,circleShiftedSecond,circleH4Derivative] using
      circle_bloch_principal_second_eq T 0 p hp f

theorem circle_principal_bloch_coefficient_apply (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p) (j : Fin 5) (f : CircleL2 T) :
    circlePrincipalBlochCoefficient T h h₁ h₂ p hp j f =
      circleBlochCoefficient T h h₁ h₂ j (circlePrincipalResolventH4 T (p^4) (by positivity) f) := by
  obtain ⟨hfirst,hsecond⟩ := principal_first_second_jets T p hp f
  have hthird := circle_principal_third_eq_jet T p (by linarith) f
  have hcoe : (circlePrincipalResolventH4 T (p^4) (by positivity) f:CircleL2 T) =
      circlePrincipalResolvent T (p^4) (by positivity) f := rfl
  fin_cases j
  · change (((p^4:ℝ):ℂ) • circlePrincipalResolvent T (p^4) (by positivity)-1+
      circleBlochLowerResolvent T h h₁ h₂ 0 p hp) f =
        circleH4Operator T h h₁ h₂ (circlePrincipalResolventH4 T (p^4) (by positivity) f)
    simp only [add_apply,sub_apply,smul_apply,one_apply_eq_self]
    have hi := circle_bloch_shift_principal T h h₁ h₂ 0 p hp f
    change ((p^4:ℝ):ℂ) • (circlePrincipalResolventH4 T (p^4) (by positivity) f:CircleL2 T)-
      circleBlochOperator T h h₁ h₂ 0 (circlePrincipalResolventH4 T (p^4) (by positivity) f) =
        f-circleBlochLowerResolvent T h h₁ h₂ 0 p hp f at hi
    rw [circle_bloch_at_zero,hcoe] at hi
    calc
      _ = ((p^4:ℝ):ℂ) • circlePrincipalResolvent T (p^4) (by positivity) f-
        (f-circleBlochLowerResolvent T h h₁ h₂ 0 p hp f) := by module
      _ = _ := by rw [← hi]; abel
  · change circlePrincipalBlochCoefficient T h h₁ h₂ p hp 1 f =
      circleBlochCoefficient T h h₁ h₂ 1 (circlePrincipalResolventH4 T (p^4) (by positivity) f)
    rw [circle_bloch_coefficient_one_apply]
    simp only [circlePrincipalBlochCoefficient,Matrix.cons_val_one,Matrix.cons_val_zero,
      Matrix.cons_val,Matrix.head_cons,Matrix.tail_cons,smul_apply,sub_apply,
      ContinuousLinearMap.comp_apply,hfirst,hthird,hcoe]
  · change circlePrincipalBlochCoefficient T h h₁ h₂ p hp 2 f =
      circleBlochCoefficient T h h₁ h₂ 2 (circlePrincipalResolventH4 T (p^4) (by positivity) f)
    rw [circle_bloch_coefficient_two_apply]
    simp only [circlePrincipalBlochCoefficient,Matrix.cons_val_one,Matrix.cons_val_zero,
      Matrix.cons_val,Matrix.head_cons,Matrix.tail_cons,smul_apply,sub_apply,
      ContinuousLinearMap.comp_apply,hsecond,hcoe]
  · change circlePrincipalBlochCoefficient T h h₁ h₂ p hp 3 f =
      circleBlochCoefficient T h h₁ h₂ 3 (circlePrincipalResolventH4 T (p^4) (by positivity) f)
    rw [circle_bloch_coefficient_three_apply]
    simp only [circlePrincipalBlochCoefficient,Matrix.cons_val_one,Matrix.cons_val_zero,
      Matrix.cons_val,Matrix.head_cons,Matrix.tail_cons,smul_apply,hfirst]
  · change circlePrincipalBlochCoefficient T h h₁ h₂ p hp 4 f =
      circleBlochCoefficient T h h₁ h₂ 4 (circlePrincipalResolventH4 T (p^4) (by positivity) f)
    rw [circle_bloch_coefficient_four_apply]
    simp only [circlePrincipalBlochCoefficient,Matrix.cons_val_one,Matrix.cons_val_zero,
      Matrix.cons_val,Matrix.head_cons,Matrix.tail_cons,smul_apply,hcoe]

noncomputable def circlePrincipalBlochFamily (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p) (z : ℂ) : CircleL2 T →L[ℂ] CircleL2 T :=
  circlePrincipalBlochCoefficient T h h₁ h₂ p hp 0+
    z • circlePrincipalBlochCoefficient T h h₁ h₂ p hp 1+
    z^2 • circlePrincipalBlochCoefficient T h h₁ h₂ p hp 2+
    z^3 • circlePrincipalBlochCoefficient T h h₁ h₂ p hp 3+
    z^4 • circlePrincipalBlochCoefficient T h h₁ h₂ p hp 4

theorem circle_principal_bloch_family_real (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p) (α : ℝ) (f : CircleL2 T) :
    circlePrincipalBlochFamily T h h₁ h₂ p hp (α:ℂ) f =
      circleBlochOperator T h h₁ h₂ α (circlePrincipalResolventH4 T (p^4) (by positivity) f) := by
  rw [circle_bloch_polynomial]
  simp only [circlePrincipalBlochFamily,add_apply,smul_apply,circle_principal_bloch_coefficient_apply]

end Lemniscate
