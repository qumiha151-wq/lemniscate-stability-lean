import Lemniscate.PeriodicEvenTailSum
import Lemniscate.PeriodicHighFourierNorm
import Lemniscate.PeriodicBlochCoefficientBounds
import Lemniscate.PeriodicFiniteVectorTail

/-! Actual high H^{-2} action bounds on the finite rotation and adjoint
correction vectors. The proof combines their low polynomials and H4 tails. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem circle_finite_vector_action_high_bound (A : circleH4Domain T →ₗ[ℂ] CircleL2 T)
    (hA : ∀ f, ‖A f‖ ≤ 200*circleAngularH4Norm T f)
    (v : Fin 15 → ℝ)
    (htail : circleAngularH4Norm T (circleFiniteSineTail T v) ≤ 1/10000)
    (hlow : (∑' n : ℤ, if Even n ∧ 32 ≤ |(n:ℝ)| then
      ‖fourierCoeff (A (circleSineTrialH4 T 10 (fun j => (v (Fin.castAdd 5 j):ℂ)))) n‖^2/
        (n:ℝ)^4 else 0) ≤ (1/8000:ℝ)^2) :
    (∑' n : ℤ, if Even n ∧ 32 ≤ |(n:ℝ)| then
      ‖fourierCoeff (A (I • circleSineTrialH4 T 15 (fun j => (v j:ℂ)))) n‖^2/
        (n:ℝ)^4 else 0) ≤ (1/5000:ℝ)^2 := by
  classical
  let S : Set ℤ := {n | Even n ∧ 32 ≤ |(n:ℝ)|}
  have hS (n : ℤ) (hn : n ∈ S) : 32 ≤ |(n:ℝ)| := hn.2
  have hl : (∑' n : ℤ, if n ∈ S then
      ‖fourierCoeff (A (circleFiniteSineLow T v)) n‖^2/(n:ℝ)^4 else 0) ≤ (1/8000:ℝ)^2 := by
    simpa only [S,Set.mem_ofPred_eq,circleFiniteSineLow,map_smul,circle_fourierCoeff_smul,
      norm_mul,Complex.norm_I,one_mul] using hlow
  have ht := circle_high_action_on_small_h4 T A hA (circleFiniteSineTail T v) htail S hS
  have hadd := circle_high_fourier_add_square_bound T (A (circleFiniteSineLow T v))
    (A (circleFiniteSineTail T v)) S hS 1 (by norm_num)
  simp only [inv_one] at hadd
  rw [circle_finite_sine_low_tail T v,map_add]
  change (∑' n : ℤ, if n ∈ S then _ else 0) ≤ _
  have hnum : (2*((1/8000:ℝ)^2+(1/51200:ℝ)^2)) ≤ (1/5000:ℝ)^2 := by norm_num
  linarith only [hadd,hl,ht,hnum]

theorem circle_bloch_finite_vector_action_bound (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (hr : (2*Real.pi/T)^2 ≤ 18/25)
    (hhbound : ‖h‖ ≤ 1) (hh₁bound : ‖h₁‖ ≤ 2) (hh₂bound : ‖h₂‖ ≤ 4)
    (v : Fin 15 → ℝ) (hv : v = rotationFiniteCoefficient ∨ v = finiteDifferenceCoefficient)
    (j : Fin 5) :
    (∑' n : ℤ, if Even n ∧ 32 ≤ |(n:ℝ)| then
      ‖fourierCoeff (circleBlochCoefficient T h h₁ h₂ j
        (I • circleSineTrialH4 T 15 (fun i => (v i:ℂ)))) n‖^2/(n:ℝ)^4 else 0) ≤ (1/5000:ℝ)^2 ∧
    (∑' n : ℤ, if Even n ∧ 32 ≤ |(n:ℝ)| then
      ‖fourierCoeff (circleBlochAdjointCoefficient T h h₁ h₂ j
        (I • circleSineTrialH4 T 15 (fun i => (v i:ℂ)))) n‖^2/(n:ℝ)^4 else 0) ≤ (1/5000:ℝ)^2 := by
  have hκ : 2*Real.pi/T ≤ 1 := by nlinarith only [hr,sq_nonneg (2*Real.pi/T-1)]
  have hAl (f : circleH4Domain T) := circle_bloch_coefficient_angular_bounds T h h₁ h₂
    hhbound hh₁bound hh₂bound hκ f
  have htail : circleAngularH4Norm T (circleFiniteSineTail T v) ≤ 1/10000 := by
    rcases hv with rfl | rfl
    · exact (circle_finite_vector_h4_tail_bounds T).1
    · exact (circle_finite_vector_h4_tail_bounds T).2
  have hl1 : (∑ i : Fin 10, ‖(v (Fin.castAdd 5 i):ℂ)‖) ≤ 5 := by
    rcases hv with rfl | rfl
    · linarith only [finite_vector_low_l1_bounds.1]
    · linarith only [finite_vector_low_l1_bounds.2]
  have hlow := circle_bloch_low_sine_high_square_bound T h h₁ h₂ hh hh₁ hreal h₁real h₂real
    hs hc hr j (fun i => (v (Fin.castAdd 5 i):ℂ)) hl1
  constructor
  · exact circle_finite_vector_action_high_bound T (circleBlochCoefficient T h h₁ h₂ j)
      (fun f => (hAl f).1 j) v htail hlow.1
  · exact circle_finite_vector_action_high_bound T (circleBlochAdjointCoefficient T h h₁ h₂ j)
      (fun f => (hAl f).2.1 j) v htail hlow.2

end Lemniscate
