import Lemniscate.PeriodicCenteredCoefficientComparison
import Lemniscate.PeriodicReducedFormComparison

/-! The constant stable coefficient uses the pullback of S0. Positive
coefficients use the exact neutral change. Compare the full reduced forms. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleExactSymmetricCoefficient (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (ψ : circleH4Domain T) (j : Fin 5) (f g : circleH4Domain T) : ℂ :=
  if j = 0 then
    inner ℂ (circleRotationHouseholderH4 T q p hq hp f:CircleL2 T)
      (circleH4SymmetricOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
        (circleRotationHouseholderH4 T q p hq hp g))
  else (1/2:ℂ)*(inner ℂ (f:CircleL2 T) (circleCenteredBlochCoefficient T q p hq hp (ψ:CircleL2 T) j g)+
    inner ℂ (circleCenteredBlochCoefficient T q p hq hp (ψ:CircleL2 T) j f) (g:CircleL2 T))

noncomputable def circleExactReducedBlochPairing (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (ψ : circleH4Domain T) (α : ℝ) (f g : circleH4Domain T) : ℂ :=
  circleReducedBlochForm T (circleExactSymmetricCoefficient T q p hq hp ψ) α f g

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
    (ψ : circleH4Domain T)
    (hψnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (hh : ‖q^2‖ ≤ 1) (hh₁ : ‖(2:ℂ) • (q*p)‖ ≤ 2)
    (hh₂ : ‖1-(3:ℂ) • (q^4)‖ ≤ 4) (hκ : 2*Real.pi/T ≤ 1)
include he hqreal hpreal hs hc ho hr hψnorm hψzero hh hh₁ hh₂ hκ

set_option maxHeartbeats 1000000 in
theorem paper_centered_coefficient_difference (j : Fin 5) (f g : circleH4Domain T) :
    ‖circleExactSymmetricCoefficient T q p hq hp ψ j f g-
      circleFiniteSymmetricCoefficient T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) j f g‖ ≤
        (1/2000:ℝ)*‖f‖*‖g‖ := by
  by_cases hj : j = 0
  · subst j
    let U := circleRotationHouseholderH4 T q p hq hp
    let UN := neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T)
    let S := circleH4SymmetricOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
    have hb (v : circleH4Domain T) := paper_neutral_input_difference_bounds T q p hq hp he
      hqreal hpreal hs hc ho hr ψ hψnorm hψzero v
    have hUδ (v : circleH4Domain T) : circleAngularH4Norm T (U v-UN v) ≤ 5000*(1/10^11:ℝ)*‖v‖ :=
      (hb v).2.2.2.2.2.2.1
    have hU (v : circleH4Domain T) : ‖U v‖ ≤ 2*‖v‖ := (hb v).2.2.2.2.2.2.2.1
    have hUN (v : circleH4Domain T) : ‖UN v‖ ≤ 2*‖v‖ := (hb v).2.2.2.2.2.2.2.2
    have hreal : ∀ x, conj ((q^2 : C(AddCircle T, ℂ)) x) = (q^2 : C(AddCircle T, ℂ)) x := by
      intro x; change conj ((q x)^2) = (q x)^2; simp only [map_pow,hqreal]
    have h₁real : ∀ x, conj (((2:ℂ) • (q*p)) x) = ((2:ℂ) • (q*p)) x := by
      intro x; change conj (2*(q x*p x)) = 2*(q x*p x); simp only [map_mul,map_ofNat,hqreal,hpreal]
    have h₂real : ∀ x, conj ((1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) x) =
        (1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) x := by
      intro x; change conj (1-3*(q x)^4) = 1-3*(q x)^4
      simp only [map_sub,map_mul,map_one,map_ofNat,map_pow,hqreal]
    have hgreen := circle_h4_symmetric_green T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circle_profile_square_deriv T q p hq) hreal h₁real h₂real
    have hS (v : circleH4Domain T) : ‖S v‖ ≤ 200*circleAngularH4Norm T v :=
      (circle_bloch_coefficient_angular_bounds T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
        hh hh₁ hh₂ hκ v).2.2
    have hest := circle_transformed_symmetric_form_difference_bound T S S hgreen hS hS
      U UN U UN (1/10^11) (by norm_num) hUδ hUδ hUN hU f g
    have hsym (v w : circleH4Domain T) :
        (1/2:ℂ)*(inner ℂ (v:CircleL2 T) (S w)+inner ℂ (S v) (w:CircleL2 T)) =
          inner ℂ (v:CircleL2 T) (S w) := by
      rw [hgreen v w]
      ring
    rw [hsym,hsym] at hest
    rw [circleExactSymmetricCoefficient,if_pos rfl,circle_finite_zero_coefficient T _ _ _
      (circle_profile_square_deriv T q p hq) (circle_profile_square_second T q p hq hp he)
      hreal h₁real h₂real]
    apply hest.trans
    nlinarith only [mul_nonneg (norm_nonneg f) (norm_nonneg g)]
  · rw [circleExactSymmetricCoefficient,if_neg hj]
    exact paper_centered_positive_coefficient_difference T q p hq hp he hqreal hpreal hs hc ho hr
      ψ hψnorm hψzero hh hh₁ hh₂ hκ j hj f g

theorem paper_exact_finite_reduced_form_difference (α : ℝ) (hα : |α| ≤ 1) (f : circleH4Domain T) :
    ‖circleExactReducedBlochPairing T q p hq hp ψ α f f-
      circleFiniteBlochPairing T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) α f f‖ ≤
        (1/100:ℝ)*‖f‖^2 := by
  exact circle_reduced_form_difference_bound T _ _
    (paper_centered_coefficient_difference T q p hq hp he hqreal hpreal hs hc ho hr
      ψ hψnorm hψzero hh hh₁ hh₂ hκ) α hα f

end Profile
end Lemniscate
