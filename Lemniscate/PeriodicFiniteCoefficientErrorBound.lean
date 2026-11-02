import Lemniscate.PeriodicFiniteChangeBounds
import Lemniscate.PeriodicFiniteCoefficientError
import Lemniscate.PeriodicRankOneHighBounds

/-! Uniform high H^{-2} control of the actual finite-rank coefficient
errors, using the compiled auxiliary-vector action and ordinary L2 bounds. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem circle_finite_coefficient_error_bound (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 ≤ 18/25)
    (hhbound : ‖h‖ ≤ 1) (hh₁bound : ‖h₁‖ ≤ 2) (hh₂bound : ‖h₂‖ ≤ 4)
    (j : Fin 3) (f : circleH4Domain T) :
    circleEvenHighSquare T (circleFiniteCoefficientError T h h₁ h₂ j f) ≤
      49*(1/5000:ℝ)^2*‖f‖^2 := by
  let e := circleFiniteRotationPhase T
  let a := circleHouseholderAnchorH4 T
  let z := circleFiniteAdjointPhaseH4 T-e
  let d := 1+inner ℂ (e:CircleL2 T) (a:CircleL2 T)
  have heA := circle_auxiliary_high_actions T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr
    hhbound hh₁bound hh₂bound e (Or.inr (Or.inl rfl))
  have haA := circle_auxiliary_high_actions T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr
    hhbound hh₁bound hh₂bound a (Or.inl rfl)
  have hzA := circle_auxiliary_high_actions T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr
    hhbound hh₁bound hh₂bound z (Or.inr (Or.inr rfl))
  have hchange := circle_finite_change_l2_bounds T
  have hu : ‖e+a‖ ≤ 2 := by
    change ‖((e+a:circleH4Domain T):CircleL2 T)‖ ≤ 2
    simpa only [e,a,Submodule.coe_add,circle_householder_anchor_h4_coe] using hchange.2.2.1
  have he : ‖e‖ ≤ 1 := by
    change ‖(circleFiniteRotationPhase T:CircleL2 T)‖ ≤ 1
    rw [(circle_finite_phase_normalization T).1]
  have hz : ‖z‖ ≤ 1 := hchange.2.1
  have hd : 1 ≤ ‖d‖ := (circle_finite_householder_hypotheses T).2.2
  have hsum (A : circleH4Domain T →ₗ[ℂ] CircleL2 T)
      (hAe : circleEvenHighSquare T (A e) ≤ (1/5000:ℝ)^2)
      (hAa : circleEvenHighSquare T (A a) ≤ (1/5000:ℝ)^2) :
      circleEvenHighSquare T (A (e+a)) ≤ 4*(1/5000:ℝ)^2 := by
    rw [map_add]
    have h := circle_even_high_square_add T (A e) (A a) 1 (by norm_num)
    simp only [inv_one] at h
    linarith only [h,hAe,hAa]
  by_cases hj : j = 0
  · subst j
    rw [circle_finite_zero_error_expansion]
    change circleEvenHighSquare T
      (-(d⁻¹*inner ℂ ((e+a:circleH4Domain T):CircleL2 T) (f:CircleL2 T)) •
        circleH4SymmetricOperator T h h₁ h₂ (e+a)) ≤ _
    have hS : circleEvenHighSquare T (circleH4SymmetricOperator T h h₁ h₂ (e+a)) ≤
        4*(1/5000:ℝ)^2 := by
      rw [← circle_bloch_symmetric_coefficient_zero T h h₁ h₂ (e+a)]
      exact hsum (circleBlochSymmetricCoefficient T h h₁ h₂ 0) (heA.2.2 0) (haA.2.2 0)
    have ht := inner_inverse_norm_bound T ((e+a:circleH4Domain T):CircleL2 T) (f:CircleL2 T) d hu hd
    have ht' : ‖-(d⁻¹*inner ℂ ((e+a:circleH4Domain T):CircleL2 T) (f:CircleL2 T))‖ ≤ 2*‖f‖ := by
      simpa only [norm_neg,Submodule.norm_coe] using ht
    have hb := circle_even_high_square_scaled_bound T _ _ (2*‖f‖) (4*(1/5000:ℝ)^2) ht' hS
    nlinarith only [hb,sq_nonneg ‖f‖]
  · have hb := four_rank_terms_high_bound T (e+a) e z f
      (neutralHouseholderDomain e a f) (neutralHouseholderAdjointDomain e a f)
      (circleBlochCoefficient T h h₁ h₂ (j.castLE (by decide)))
      (circleBlochAdjointCoefficient T h h₁ h₂ (j.castLE (by decide))) d (1/5000)
      hd hu he hz (hchange.2.2.2 f).1 (hchange.2.2.2 f).2
      (hsum _ (heA.1 _) (haA.1 _)) (hsum _ (heA.2.1 _) (haA.2.1 _)) (hzA.2.1 _) (heA.1 _)
    rw [circle_finite_positive_error_expansion T h h₁ h₂ j hj]
    exact hb

end Lemniscate
