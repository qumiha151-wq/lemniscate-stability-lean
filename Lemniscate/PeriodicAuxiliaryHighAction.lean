import Lemniscate.PeriodicEvenHighSquare
import Lemniscate.PeriodicFiniteVectorAction
import Lemniscate.PeriodicSymmetricCoefficient
import Lemniscate.PeriodicFiniteCouplingTest

/-! High H^{-2} bounds for the actual anchor, finite rotation and finite
adjoint correction, including their symmetric Bloch coefficients. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem circle_anchor_low_sine_representation :
    circleSineTrialH4 T 10 (fun j => if j = 0 then I else 0) = circleHouseholderAnchorH4 T := by
  have heq : circleSineTrialH4 T 10 (fun j => if j = 0 then I else 0) = I • circleSineH4 T 0 := by
    unfold circleSineTrialH4
    have hsum := Finset.sum_eq_single (0:Fin 10)
      (f := fun j => (if j = 0 then I else 0) • circleSineH4 T j.val)
      (s := Finset.univ)
      (fun j _ hj => by simp only [if_neg hj,zero_smul])
      (by simp)
    simpa only [if_true,Fin.val_zero] using hsum
  rw [heq]
  have hfactor : I*evenSineFactor = evenCosineFactor := by simp [evenSineFactor,← mul_assoc]
  simp only [circleSineH4,smul_smul,hfactor]
  rfl

theorem circle_finite_adjoint_correction_sine :
    circleFiniteAdjointPhaseH4 T-circleFiniteRotationPhase T =
      I • circleSineTrialH4 T 15 (fun j => (finiteDifferenceCoefficient j:ℂ)) := by
  simp only [circleFiniteAdjointPhaseH4,circleFiniteRotationPhase,circleAdjointApproximation,
    circleRotationApproximation,circleSineTrialH4,finiteDifferenceCoefficient,
    Complex.ofReal_sub,sub_smul,Finset.sum_sub_distrib,smul_sub]

theorem circle_symmetric_high_action_of_raw_bounds (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 3) (f : circleH4Domain T) (ε : ℝ)
    (hraw : circleEvenHighSquare T
      (circleBlochCoefficient T h h₁ h₂ (j.castLE (by decide)) f) ≤ ε^2)
    (hadj : circleEvenHighSquare T
      (circleBlochAdjointCoefficient T h h₁ h₂ (j.castLE (by decide)) f) ≤ ε^2) :
    circleEvenHighSquare T (circleBlochSymmetricCoefficient T h h₁ h₂ j f) ≤ ε^2 := by
  change circleEvenHighSquare T ((1/2:ℂ) •
    (circleBlochCoefficient T h h₁ h₂ (j.castLE (by decide)) f+
      circleBlochAdjointCoefficient T h h₁ h₂ (j.castLE (by decide)) f)) ≤ _
  rw [circle_even_high_square_smul]
  have hnorm : ‖(1/2:ℂ)‖^2 = (1/4:ℝ) := by norm_num
  rw [hnorm]
  have hsum := circle_even_high_square_add T
    (circleBlochCoefficient T h h₁ h₂ (j.castLE (by decide)) f)
    (circleBlochAdjointCoefficient T h h₁ h₂ (j.castLE (by decide)) f) 1 (by norm_num)
  simp only [inv_one] at hsum
  linarith only [hsum,hraw,hadj]

section Profile
variable (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 ≤ 18/25)
include hh hh₁ hreal h₁real h₂real hs hc hr

theorem circle_bloch_anchor_high_action (j : Fin 5) :
    circleEvenHighSquare T (circleBlochCoefficient T h h₁ h₂ j (circleHouseholderAnchorH4 T)) ≤ (1/5000:ℝ)^2 ∧
    circleEvenHighSquare T (circleBlochAdjointCoefficient T h h₁ h₂ j (circleHouseholderAnchorH4 T)) ≤ (1/5000:ℝ)^2 := by
  have hl1 : (∑ j : Fin 10, ‖if j = 0 then I else 0‖) ≤ (5:ℝ) := by
    have he (i : Fin 10) : ‖if i = 0 then I else 0‖ = if i = 0 then (1:ℝ) else 0 := by
      split_ifs <;> norm_num
    simp only [he]
    norm_num
  have hb := circle_bloch_low_sine_high_square_bound T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr
    j (fun i => if i = 0 then I else 0) hl1
  rw [circle_anchor_low_sine_representation] at hb
  change circleEvenHighSquare T _ ≤ _ ∧ circleEvenHighSquare T _ ≤ _ at hb
  constructor <;> linarith only [hb.1,hb.2]

theorem circle_auxiliary_high_actions (hhbound : ‖h‖ ≤ 1) (hh₁bound : ‖h₁‖ ≤ 2) (hh₂bound : ‖h₂‖ ≤ 4)
    (f : circleH4Domain T)
    (hf : f = circleHouseholderAnchorH4 T ∨ f = circleFiniteRotationPhase T ∨
      f = circleFiniteAdjointPhaseH4 T-circleFiniteRotationPhase T) :
    (∀ j : Fin 5, circleEvenHighSquare T (circleBlochCoefficient T h h₁ h₂ j f) ≤ (1/5000:ℝ)^2) ∧
    (∀ j : Fin 5, circleEvenHighSquare T (circleBlochAdjointCoefficient T h h₁ h₂ j f) ≤ (1/5000:ℝ)^2) ∧
    (∀ j : Fin 3, circleEvenHighSquare T (circleBlochSymmetricCoefficient T h h₁ h₂ j f) ≤ (1/5000:ℝ)^2) := by
  have hb (j : Fin 5) :
      circleEvenHighSquare T (circleBlochCoefficient T h h₁ h₂ j f) ≤ (1/5000:ℝ)^2 ∧
      circleEvenHighSquare T (circleBlochAdjointCoefficient T h h₁ h₂ j f) ≤ (1/5000:ℝ)^2 := by
    rcases hf with rfl | rfl | rfl
    · exact circle_bloch_anchor_high_action T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr j
    · simpa only [circleEvenHighSquare,circleFiniteRotationPhase,circleRotationApproximation] using
        circle_bloch_finite_vector_action_bound T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr
          hhbound hh₁bound hh₂bound rotationFiniteCoefficient (Or.inl rfl) j
    · rw [circle_finite_adjoint_correction_sine]
      exact circle_bloch_finite_vector_action_bound T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr
        hhbound hh₁bound hh₂bound finiteDifferenceCoefficient (Or.inr rfl) j
  refine ⟨fun j => (hb j).1,fun j => (hb j).2,fun j => ?_⟩
  exact circle_symmetric_high_action_of_raw_bounds T h h₁ h₂ j f (1/5000)
    (hb _).1 (hb _).2

end Profile
end Lemniscate
