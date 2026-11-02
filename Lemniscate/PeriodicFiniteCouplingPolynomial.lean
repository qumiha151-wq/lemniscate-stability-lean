import Lemniscate.PeriodicFiniteCouplingSupport
import Lemniscate.PeriodicFourierCoupling
import Lemniscate.PeriodicFiniteBlochMatrix
import Lemniscate.PeriodicFiniteBlochDecomposition

/-! The actual high-low reduced pairing is quadratic in the Bloch parameter.
Its three L2 test coefficients are used by the analytic coupling estimate. -/
namespace Lemniscate
open Complex Matrix MeasureTheory
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleFiniteCouplingTestCoefficient (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 3) (v : Fin 31 → ℂ) : CircleL2 T :=
  let f := circleEvenHeadH4 T v
  let f₀ := circleFixedProjectionH4 T f
  let f₁ := f-f₀
  let X := circleFiniteCoefficientTest T h h₁ h₂
  ![X 0 f₁+X 1 f₀, X 1 f₁+X 2 f₀, X 2 f₁] j

theorem circle_finite_coupling_polynomial (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) (α : ℝ) (v : Fin 31 → ℂ)
    (y : circleH4Domain T)
    (hy : ∀ n : ℤ, |(n:ℝ)| < 32 → fourierCoeff (y:CircleL2 T) n = 0) :
    circleFiniteBlochPairing T h h₁ h₂ α (circleEvenHeadH4 T v) y =
      inner ℂ (circleFiniteCouplingTestCoefficient T h h₁ h₂ 0 v+
        (α:ℂ) • circleFiniteCouplingTestCoefficient T h h₁ h₂ 1 v+
        (α:ℂ)^2 • circleFiniteCouplingTestCoefficient T h h₁ h₂ 2 v) (y:CircleL2 T) := by
  change circleFiniteBlochPairing T h h₁ h₂ α (circleEvenHeadH4 T v) y =
    inner ℂ (circleFiniteCoefficientTest T h h₁ h₂ 0
        (circleEvenHeadH4 T v-circleFixedProjectionH4 T (circleEvenHeadH4 T v))+
      circleFiniteCoefficientTest T h h₁ h₂ 1 (circleFixedProjectionH4 T (circleEvenHeadH4 T v))+
      (α:ℂ) • (circleFiniteCoefficientTest T h h₁ h₂ 1
        (circleEvenHeadH4 T v-circleFixedProjectionH4 T (circleEvenHeadH4 T v))+
        circleFiniteCoefficientTest T h h₁ h₂ 2 (circleFixedProjectionH4 T (circleEvenHeadH4 T v)))+
      (α:ℂ)^2 • circleFiniteCoefficientTest T h h₁ h₂ 2
        (circleEvenHeadH4 T v-circleFixedProjectionH4 T (circleEvenHeadH4 T v))) (y:CircleL2 T)
  have hP : circleFixedProjectionH4 T y = 0 := by
    rw [circleFixedProjectionH4, circle_householder_anchor_pairing,
      hy 2 (by norm_num), hy (-2) (by norm_num)]
    simp
  have hz (j : Fin 5) (u : circleH4Domain T) :
      circleFiniteSymmetricCoefficient T h h₁ h₂ j u 0 = 0 := by
    have heq := circle_finite_symmetric_add_right T h h₁ h₂ j u 0 0
    simp only [add_zero] at heq
    linear_combination -heq
  have hLow (w : Fin 31 → ℂ) : inner ℂ (circleEvenHeadH4 T w:CircleL2 T) (y:CircleL2 T) = 0 := by
    have hb (i : Fin 31) : inner ℂ (fourierBasis (T := T) (evenHeadFrequency i)) (y:CircleL2 T) = 0 := by
      rw [← HilbertBasis.repr_apply_apply, fourierBasis_repr]
      exact hy _ ((even_head_frequency_range _).mp ⟨i, rfl⟩).2
    rw [circle_even_head_h4_coe]
    simp only [sum_inner, inner_smul_left, hb, mul_zero, Finset.sum_const_zero]
  have hThree (w : Fin 31 → ℂ) :
      inner ℂ (circleFiniteCoefficientTest T h h₁ h₂ 3 (circleEvenHeadH4 T w)) (y:CircleL2 T) = 0 := by
    rw [← (circle_fourier_pairing_hasSum T _ (y:CircleL2 T)).tsum_eq]
    have hterm (n : ℤ) :
        conj (fourierCoeff (circleFiniteCoefficientTest T h h₁ h₂ 3 (circleEvenHeadH4 T w)) n)*
          fourierCoeff (y:CircleL2 T) n = 0 := by
      by_cases hn : |(n:ℝ)| < 32
      · rw [hy n hn, mul_zero]
      · rw [circle_finite_third_test_fourier_zero T h h₁ h₂ w n (le_of_not_gt hn)]
        simp only [map_zero, zero_mul]
    simp only [hterm, tsum_zero]
  have hTest (j : Fin 5) (u : circleH4Domain T) :=
    circle_finite_coefficient_high_test T h h₁ h₂ hh hh₁ hreal h₁real h₂real j u y hy
  dsimp only [circleFiniteBlochPairing]
  simp only [hP, sub_zero, hz, Submodule.coe_zero, inner_zero_right, mul_zero, add_zero, zero_add]
  simp only [circle_stable_projection_head]
  simp only [circle_fixed_projection_head]
  simp only [hTest, hThree, hLow, inner_add_left, inner_smul_left,
    Complex.conj_ofReal, map_pow]
  ring

end Lemniscate
