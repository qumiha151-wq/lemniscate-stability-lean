import Lemniscate.PeriodicFiniteCoefficientErrorBound
import Lemniscate.PeriodicFiniteProjectionL2
import Lemniscate.PeriodicFiniteCouplingPolynomial

/-! The actual reduced tests split into the unprojected symmetric baseline,
projected finite-rank errors, and an explicit rank-one projection error. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
set_option maxHeartbeats 1000000
variable (T : ℝ) [Fact (0 < T)]

private theorem projected_three_square_bound (R : Fin 3 → circleH4Domain T → CircleL2 T)
    (f₀ f₁ : circleH4Domain T) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ j g, circleEvenHighSquare T (R j g) ≤ C*‖g‖^2) :
    circleEvenHighSquare T (R 0 f₁+R 1 f₀)+
      (circleEvenHighSquare T (R 1 f₁+R 2 f₀)+circleEvenHighSquare T (R 2 f₁)) ≤
        5*C*(‖f₁‖^2+‖f₀‖^2) := by
  have h0 := circle_even_high_square_add T (R 0 f₁) (R 1 f₀) 1 (by norm_num)
  have h1 := circle_even_high_square_add T (R 1 f₁) (R 2 f₀) 1 (by norm_num)
  simp only [inv_one] at h0 h1
  nlinarith only [h0,h1,hb 0 f₁,hb 1 f₀,hb 1 f₁,hb 2 f₀,hb 2 f₁,
    mul_nonneg hC (sq_nonneg ‖f₀‖)]

noncomputable def circleProjectedCoefficientError (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 3) (f : circleH4Domain T) : CircleL2 T :=
  let f₀ := circleFixedProjectionH4 T f
  let f₁ := f-f₀
  let R := circleFiniteCoefficientError T h h₁ h₂
  ![R 0 f₁+R 1 f₀,R 1 f₁+R 2 f₀,R 2 f₁] j

noncomputable def circleSymmetricProjectionError (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 3) (f : circleH4Domain T) : CircleL2 T :=
  let a := circleHouseholderAnchorH4 T
  let S := circleBlochSymmetricCoefficient T h h₁ h₂
  inner ℂ (circleHouseholderAnchor T) (f:CircleL2 T) •
    ![S 1 a-S 0 a,S 2 a-S 1 a,-S 2 a] j

theorem circle_finite_test_error_decomposition (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 3) (v : Fin 31 → ℂ) :
    circleFiniteCouplingTestCoefficient T h h₁ h₂ j v =
      circleBlochSymmetricCoefficient T h h₁ h₂ j (circleEvenHeadH4 T v)+
        circleProjectedCoefficientError T h h₁ h₂ j (circleEvenHeadH4 T v)+
        circleSymmetricProjectionError T h h₁ h₂ j (circleEvenHeadH4 T v) := by
  let f := circleEvenHeadH4 T v
  let a := circleHouseholderAnchorH4 T
  let t := inner ℂ (circleHouseholderAnchor T) (f:CircleL2 T)
  let X := circleFiniteCoefficientTest T h h₁ h₂
  let S := circleBlochSymmetricCoefficient T h h₁ h₂
  fin_cases j <;>
    simp only [circleFiniteCouplingTestCoefficient,circleProjectedCoefficientError,
      circleSymmetricProjectionError,circleFiniteCoefficientError,circleFixedProjectionH4,
      Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_zero,Matrix.cons_val_succ,
      Fin.castLE,Fin.val_zero,Fin.val_one,Fin.val_ofNat,map_sub,map_smul]
  · change X 0 (f-t • a)+X 1 (t • a) =
      S 0 f+((X 0 (f-t • a)-(S 0 f-t • S 0 a))+(X 1 (t • a)-t • S 1 a))+
        t • (S 1 a-S 0 a)
    module
  · change X 1 (f-t • a)+X 2 (t • a) =
      S 1 f+((X 1 (f-t • a)-(S 1 f-t • S 1 a))+(X 2 (t • a)-t • S 2 a))+
        t • (S 2 a-S 1 a)
    module
  · change X 2 (f-t • a) = S 2 f+(X 2 (f-t • a)-(S 2 f-t • S 2 a))+t • (-S 2 a)
    module

section Profile
variable (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 ≤ 18/25)
    (hhbound : ‖h‖ ≤ 1) (hh₁bound : ‖h₁‖ ≤ 2) (hh₂bound : ‖h₂‖ ≤ 4)
include hh hh₁ hreal h₁real h₂real hs hc hr hhbound hh₁bound hh₂bound

theorem circle_projected_coefficient_error_bound (v : Fin 31 → ℂ) :
    (∑ j : Fin 3, circleEvenHighSquare T
      (circleProjectedCoefficientError T h h₁ h₂ j (circleEvenHeadH4 T v))) ≤
        (63/5000:ℝ)^2*(∑ i : Fin 31, (evenFactorPenalty i:ℝ)*‖v i‖^2) := by
  let f := circleEvenHeadH4 T v
  let f₀ := circleFixedProjectionH4 T f
  let f₁ := f-f₀
  let R := circleFiniteCoefficientError T h h₁ h₂
  have hb (j : Fin 3) (g : circleH4Domain T) :
      circleEvenHighSquare T (R j g) ≤ 49*(1/5000:ℝ)^2*‖g‖^2 :=
    circle_finite_coefficient_error_bound T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr
      hhbound hh₁bound hh₂bound j g
  have hproject := projected_three_square_bound T R f₀ f₁ (49*(1/5000:ℝ)^2) (by positivity) hb
  have hsplit : ‖f₁‖^2+‖f₀‖^2 = ‖f‖^2 := circle_fixed_projection_l2_norm_split T f
  have hweight := circle_even_head_norm_le_weighted_energy T v
  change ‖f‖^2 ≤ 16*(∑ i : Fin 31, (evenFactorPenalty i:ℝ)*‖v i‖^2) at hweight
  conv_lhs => simp only [circleProjectedCoefficientError,Fin.sum_univ_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero]
  change circleEvenHighSquare T (R 0 f₁+R 1 f₀)+
    (circleEvenHighSquare T (R 1 f₁+R 2 f₀)+circleEvenHighSquare T (R 2 f₁)) ≤ _
  rw [hsplit] at hproject
  nlinarith only [hproject,hweight]

theorem circle_symmetric_projection_error_bound (v : Fin 31 → ℂ) :
    (∑ j : Fin 3, circleEvenHighSquare T
      (circleSymmetricProjectionError T h h₁ h₂ j (circleEvenHeadH4 T v))) ≤
        (12/5000:ℝ)^2*(∑ i : Fin 31, (evenFactorPenalty i:ℝ)*‖v i‖^2) := by
  let f := circleEvenHeadH4 T v
  let a := circleHouseholderAnchorH4 T
  let S := circleBlochSymmetricCoefficient T h h₁ h₂
  let t := inner ℂ (circleHouseholderAnchor T) (f:CircleL2 T)
  have ha := circle_auxiliary_high_actions T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr
    hhbound hh₁bound hh₂bound a (Or.inl rfl)
  have ht : ‖t‖ ≤ ‖f‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) (circleHouseholderAnchor T) (f:CircleL2 T)
    rw [(circle_finite_change_l2_bounds T).1] at h
    simpa only [t,one_mul,Submodule.norm_coe] using h
  have h01 : circleEvenHighSquare T (S 1 a-S 0 a) ≤ 4*(1/5000:ℝ)^2 := by
    have h := circle_even_high_square_add T (S 1 a) (-S 0 a) 1 (by norm_num)
    simp only [circle_even_high_square_neg,inv_one] at h
    rw [sub_eq_add_neg]
    linarith only [h,ha.2.2 1,ha.2.2 0]
  have h12 : circleEvenHighSquare T (S 2 a-S 1 a) ≤ 4*(1/5000:ℝ)^2 := by
    have h := circle_even_high_square_add T (S 2 a) (-S 1 a) 1 (by norm_num)
    simp only [circle_even_high_square_neg,inv_one] at h
    rw [sub_eq_add_neg]
    linarith only [h,ha.2.2 2,ha.2.2 1]
  have h2 : circleEvenHighSquare T (-S 2 a) ≤ (1/5000:ℝ)^2 := by
    rw [circle_even_high_square_neg]
    exact ha.2.2 2
  have hb0 := circle_even_high_square_scaled_bound T t (S 1 a-S 0 a) ‖f‖ _ ht h01
  have hb1 := circle_even_high_square_scaled_bound T t (S 2 a-S 1 a) ‖f‖ _ ht h12
  have hb2 := circle_even_high_square_scaled_bound T t (-S 2 a) ‖f‖ _ ht h2
  have hweight := circle_even_head_norm_le_weighted_energy T v
  change ‖f‖^2 ≤ 16*(∑ i : Fin 31, (evenFactorPenalty i:ℝ)*‖v i‖^2) at hweight
  conv_lhs => simp only [circleSymmetricProjectionError,Fin.sum_univ_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero]
  change circleEvenHighSquare T (t • (S 1 a-S 0 a))+
    (circleEvenHighSquare T (t • (S 2 a-S 1 a))+circleEvenHighSquare T (t • (-S 2 a))) ≤ _
  nlinarith only [hb0,hb1,hb2,hweight]

end Profile
end Lemniscate
