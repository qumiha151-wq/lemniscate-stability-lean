import Lemniscate.PeriodicProjectedTestErrors
import Lemniscate.PeriodicSymmetricBaseline
import Lemniscate.PeriodicFiniteCouplingBound

/-! The actual analytic low-high coupling estimate. Every test-function
bound is derived from the profile; no quantitative coupling premise remains. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
set_option maxHeartbeats 1000000
variable (T : ℝ) [Fact (0 < T)]

section Profile
variable (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (hr : (2*Real.pi/T)^2 ≤ 18/25)
    (hhbound : ‖h‖ ≤ 1) (hh₁bound : ‖h₁‖ ≤ 2) (hh₂bound : ‖h₂‖ ≤ 4)
include hh hh₁ hreal h₁real h₂real hs hc hr hhbound hh₁bound hh₂bound

theorem circle_finite_joint_test_bound (v : Fin 31 → ℂ) :
    (∑ j : Fin 3, circleEvenHighSquare T (circleFiniteCouplingTestCoefficient T h h₁ h₂ j v)) ≤
      (∑ i : Fin 31, (evenFactorPenalty i:ℝ)*‖v i‖^2)/8 := by
  let f := circleEvenHeadH4 T v
  let E : ℝ := ∑ i : Fin 31, (evenFactorPenalty i:ℝ)*‖v i‖^2
  let S (j : Fin 3) := circleBlochSymmetricCoefficient T h h₁ h₂ j f
  let R (j : Fin 3) := circleProjectedCoefficientError T h h₁ h₂ j f
  let P (j : Fin 3) := circleSymmetricProjectionError T h h₁ h₂ j f
  have hweight : ‖f‖^2 ≤ 16*E := circle_even_head_norm_le_weighted_energy T v
  have hE : 0 ≤ E := by linarith only [hweight,sq_nonneg ‖f‖]
  have hbase : (∑ j : Fin 3, circleEvenHighSquare T (S j)) ≤ (1/9)*E :=
    circle_symmetric_baseline_bound T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr v
  have hR : (∑ j : Fin 3, circleEvenHighSquare T (R j)) ≤ (63/5000:ℝ)^2*E :=
    circle_projected_coefficient_error_bound T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr
      hhbound hh₁bound hh₂bound v
  have hP : (∑ j : Fin 3, circleEvenHighSquare T (P j)) ≤ (12/5000:ℝ)^2*E :=
    circle_symmetric_projection_error_bound T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr
      hhbound hh₁bound hh₂bound v
  have herr : (∑ j : Fin 3, circleEvenHighSquare T (R j+P j)) ≤ (75/5000:ℝ)^2*E := by
    have hsum := Finset.sum_le_sum (s := (Finset.univ:Finset (Fin 3)))
      (fun j _ => circle_even_high_square_add T (R j) (P j) (4/21) (by norm_num))
    simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hsum
    norm_num only at hsum
    nlinarith only [hsum,hR,hP]
  have htest (j : Fin 3) :
      circleEvenHighSquare T (circleFiniteCouplingTestCoefficient T h h₁ h₂ j v) ≤
        (11/10:ℝ)*circleEvenHighSquare T (S j)+11*circleEvenHighSquare T (R j+P j) := by
    rw [circle_finite_test_error_decomposition T h h₁ h₂ j v,add_assoc]
    have h := circle_even_high_square_add T (S j) (R j+P j) (1/10) (by norm_num)
    norm_num only at h
    exact h
  have hsum := Finset.sum_le_sum (s := (Finset.univ:Finset (Fin 3))) (fun j _ => htest j)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  have hnum : ((11/10:ℝ)*(1/9)+11*(75/5000:ℝ)^2) ≤ 1/8 := by
    have h : (((11/10)*(1/9)+11*(75/5000)^2:ℚ):ℝ) ≤ ((1/8:ℚ):ℝ) :=
      Rat.cast_le.mpr even_analytic_coupling_constants.2.2.2
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_pow] using h
  have hnumE := mul_le_mul_of_nonneg_right hnum hE
  change (∑ j : Fin 3, circleEvenHighSquare T (circleFiniteCouplingTestCoefficient T h h₁ h₂ j v)) ≤ E/8
  nlinarith only [hsum,hbase,herr,hnumE]

theorem circle_finite_analytic_coupling (α : ℝ) (hα : |α| ≤ 1/2)
    (v : Fin 31 → ℂ) (y : circleH4Domain T)
    (hyeven : ∀ n : ℤ, ¬Even n → fourierCoeff (y:CircleL2 T) n = 0)
    (hyhigh : ∀ n : ℤ, |(n:ℝ)| < 32 → fourierCoeff (y:CircleL2 T) n = 0) :
    ‖circleFiniteBlochPairing T h h₁ h₂ α (circleEvenHeadH4 T v) y‖^2 ≤
      ((∑ i : Fin 31, (evenFactorPenalty i:ℝ)*‖v i‖^2)/4)*
        (∑' n : ℤ, (n:ℝ)^4*‖fourierCoeff (y:CircleL2 T) n‖^2) := by
  classical
  let S : Set ℤ := {n | Even n ∧ 32 ≤ |(n:ℝ)|}
  have hy (n : ℤ) (hn : n ∉ S) : fourierCoeff (y:CircleL2 T) n = 0 := by
    by_cases he : Even n
    · apply hyhigh n
      by_contra hnot
      exact hn ⟨he,le_of_not_gt hnot⟩
    · exact hyeven n he
  exact circle_finite_coupling_of_test_estimate T h h₁ h₂ hh hh₁ hreal h₁real h₂real
    α hα v y S (fun n hn => hn.2) hy _
      (circle_finite_joint_test_bound T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr
        hhbound hh₁bound hh₂bound v)

end Profile
end Lemniscate
