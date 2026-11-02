import Lemniscate.PeriodicExactCongruence
import Lemniscate.PeriodicExactEvenCoercivity

/-! The actual centered Bloch energy on every even H4 input. No finite
Fourier restriction or assumed energy-comparison estimate remains. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem circle_center_dilation_even (α : ℝ) (f : circleH4Domain T)
    (hf : ∀ n : ℤ, Odd n → fourierCoeff (f:CircleL2 T) n = 0)
    (n : ℤ) (hn : Odd n) :
    fourierCoeff (circleCenterDilation T α f:CircleL2 T) n = 0 := by
  have hn2 : n ≠ 2 := by obtain ⟨k,hk⟩ := hn; omega
  have hnneg2 : n ≠ -2 := by obtain ⟨k,hk⟩ := hn; omega
  have hP : fourierCoeff (circleFixedProjectionH4 T f:CircleL2 T) n = 0 := by
    change fourierCoeff (inner ℂ (circleHouseholderAnchor T) (f:CircleL2 T) • circleHouseholderAnchor T) n = 0
    rw [circle_fourierCoeff_smul,circle_householder_anchor_fourier]
    simp only [if_neg hn2,if_neg hnneg2,sub_self,mul_zero]
  change fourierCoeff ((α:ℂ) • (circleFixedProjectionH4 T f:CircleL2 T)+
    ((f:CircleL2 T)-(circleFixedProjectionH4 T f:CircleL2 T))) n = 0
  rw [circle_fourierCoeff_add,circle_fourierCoeff_smul,circle_fourierCoeff_sub,hP,hf n hn]
  ring

theorem circle_center_dilation_norm_sq (α : ℝ) (f : circleH4Domain T) :
    ‖circleCenterDilation T α f‖^2 = α^2*‖circleFixedProjectionH4 T f‖^2+
      ‖f-circleFixedProjectionH4 T f‖^2 := by
  have h := circle_fixed_projection_l2_norm_split T (circleCenterDilation T α f)
  rw [circle_center_dilation_remainder,circle_center_dilation_projection,norm_smul,
    Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs] at h
  linarith only [h]

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = thetaParameter)
include he hqreal hpreal hs hc ho hr

theorem paper_centered_even_energy (ψ : circleH4Domain T)
    (hnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1)
    (hzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (hd : HasCircleNeutralDecomposition T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circleUnitRotationH4 T q p hq hp) (ψ:CircleL2 T))
    (α : ℝ) (hα0 : 0 ≤ α) (hαhalf : α ≤ 1/2)
    (f : circleH4Domain T)
    (hf : ∀ n : ℤ, Odd n → fourierCoeff (f:CircleL2 T) n = 0) :
    (inner ℂ (f:CircleL2 T) (circleCenteredBlochOperator T q p hq hp (ψ:CircleL2 T) α f)).re ≤
      -(1/2:ℝ)*(α^2*‖circleFixedProjectionH4 T f‖^2+‖f-circleFixedProjectionH4 T f‖^2) := by
  have hsector := paper_single_period_adjoint_vector_sector T q p hq hp he hqreal hpreal hs hc ho hr ψ hnorm hzero
  have h := paper_exact_reduced_even_coercivity T q p hq hp he hqreal hpreal hs hc ho hr ψ hnorm hzero
    α hα0 hαhalf (circleCenterDilation T α f) (circle_center_dilation_even T α f hf)
  rw [← paper_exact_centered_energy_congruence T q p hq hp he hqreal hpreal hs hc ho hr ψ hd hnorm hsector] at h
  change _ ≤ -(1/2:ℝ)*‖circleCenterDilation T α f‖^2 at h
  rwa [circle_center_dilation_norm_sq] at h

theorem paper_centered_even_energy_exists :
    ∃ ψ : circleH4Domain T,
      inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1 ∧
      circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0 ∧
      ∀ α : ℝ, 0 ≤ α → α ≤ 1/2 → ∀ f : circleH4Domain T,
        (∀ n : ℤ, Odd n → fourierCoeff (f:CircleL2 T) n = 0) →
        (inner ℂ (f:CircleL2 T) (circleCenteredBlochOperator T q p hq hp (ψ:CircleL2 T) α f)).re ≤
          -(1/2:ℝ)*(α^2*‖circleFixedProjectionH4 T f‖^2+‖f-circleFixedProjectionH4 T f‖^2) := by
  obtain ⟨ψ,hnorm,hzero,_,_,hd⟩ := paper_single_period_neutral_decomposition T q p hq hp he hqreal hpreal hs hc ho hr
  exact ⟨ψ,hnorm,hzero,paper_centered_even_energy T q p hq hp he hqreal hpreal hs hc ho hr ψ hnorm hzero hd⟩

end Profile
end Lemniscate
