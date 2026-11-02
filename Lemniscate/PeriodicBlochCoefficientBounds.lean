import Lemniscate.PeriodicBlochGreen
import Lemniscate.PeriodicAngularH4Norm
import Lemniscate.PeriodicProfileBounds

/-! A coarse common H4-to-L2 bound for the actual Bloch coefficients and
their formal adjoints. The coefficient estimates are only 1,2,4. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem circle_h4_derivative_sum_le_angular (hκ : 2*Real.pi/T ≤ 1) (f : circleH4Domain T) :
    ‖(f:CircleL2 T)‖+‖(circleH4Jet T f).first‖+‖(circleH4Jet T f).second‖+
      ‖(circleH4Jet T f).third‖+‖(circleH4Jet T f).fourth‖ ≤ circleAngularH4Norm T f := by
  have hκpos : 0 < 2*Real.pi/T := by have := (Fact.out : 0 < T); positivity
  let k : ℝ := (2*Real.pi/T)⁻¹
  have hk : 1 ≤ k := by
    have h := mul_le_mul_of_nonneg_left hκ (inv_nonneg.mpr hκpos.le)
    simpa only [inv_mul_cancel₀ (ne_of_gt hκpos), mul_one] using h
  have hp (j : ℕ) : 1 ≤ k^j := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hk j
  have h1 := mul_le_mul_of_nonneg_right (hp 1) (norm_nonneg (circleH4Jet T f).first)
  have h2 := mul_le_mul_of_nonneg_right (hp 2) (norm_nonneg (circleH4Jet T f).second)
  have h3 := mul_le_mul_of_nonneg_right (hp 3) (norm_nonneg (circleH4Jet T f).third)
  have h4 := mul_le_mul_of_nonneg_right (hp 4) (norm_nonneg (circleH4Jet T f).fourth)
  simp only [one_mul, pow_one] at h1 h2 h3 h4
  change _ ≤ ‖(f:CircleL2 T)‖+k*‖(circleH4Jet T f).first‖+k^2*‖(circleH4Jet T f).second‖+
    k^3*‖(circleH4Jet T f).third‖+k^4*‖(circleH4Jet T f).fourth‖
  linarith only [h1,h2,h3,h4]

theorem circle_bloch_zero_raw_apply (h h₁ h₂ : C(AddCircle T, ℂ)) (f : circleH4Domain T) :
    circleBlochCoefficient T h h₁ h₂ 0 f =
      (-4:ℂ) • (circleH4Jet T f).fourth-(45:ℂ) • circleMultiplyL2 T h (circleH4Jet T f).second-
      (75/2:ℂ) • circleMultiplyL2 T h₁ (circleH4Jet T f).first-(42:ℂ) • (f:CircleL2 T)+
      (15/2:ℂ) • circleMultiplyL2 T h₂ (f:CircleL2 T) := by
  rw [circle_bloch_coefficient_zero, circle_h4_operator_apply]
  unfold circleLinearL2Expression circleSymmetricL2Expression
  module

theorem circle_bloch_adjoint_one_apply (h h₁ h₂ : C(AddCircle T, ℂ)) (f : circleH4Domain T) :
    circleBlochAdjointCoefficient T h h₁ h₂ 1 f = circleFrequencyFactor T 1 •
      ((-16:ℂ) • (circleH4Jet T f).third-(90:ℂ) • circleMultiplyL2 T h (circleH4Jet T f).first-
        (105/2:ℂ) • circleMultiplyL2 T h₁ (f:CircleL2 T)) := by
  change circleBlochCoefficient T h h₁ h₂ 1 f-
    (15*circleFrequencyFactor T 1) • circleMultiplyL2 T h₁ (f:CircleL2 T) = _
  rw [circle_bloch_coefficient_one_apply]
  module

private theorem norm_five_terms {E : Type*} [NormedAddCommGroup E] (a b c d e : E) :
    ‖a-b-c-d+e‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖+‖e‖ := by
  have h1 := norm_sub_le a b
  have h2 := norm_sub_le (a-b) c
  have h3 := norm_sub_le (a-b-c) d
  have h4 := norm_add_le (a-b-c-d) e
  linarith only [h1,h2,h3,h4]

set_option maxHeartbeats 2000000 in
theorem circle_bloch_coefficient_angular_bounds (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : ‖h‖ ≤ 1) (hh₁ : ‖h₁‖ ≤ 2) (hh₂ : ‖h₂‖ ≤ 4)
    (hκ : 2*Real.pi/T ≤ 1) (f : circleH4Domain T) :
    (∀ j : Fin 5, ‖circleBlochCoefficient T h h₁ h₂ j f‖ ≤ 200*circleAngularH4Norm T f) ∧
    (∀ j : Fin 5, ‖circleBlochAdjointCoefficient T h h₁ h₂ j f‖ ≤ 200*circleAngularH4Norm T f) ∧
    ‖circleH4SymmetricOperator T h h₁ h₂ f‖ ≤ 200*circleAngularH4Norm T f := by
  have hD := circle_h4_derivative_sum_le_angular T hκ f
  have n0 := norm_nonneg (f:CircleL2 T)
  have n1 := norm_nonneg (circleH4Jet T f).first
  have n2 := norm_nonneg (circleH4Jet T f).second
  have n3 := norm_nonneg (circleH4Jet T f).third
  have n4 := norm_nonneg (circleH4Jet T f).fourth
  have mh (u : CircleL2 T) : ‖circleMultiplyL2 T h u‖ ≤ ‖u‖ := by
    have hm := (circle_multiply_l2_norm_le T h u).trans
      (mul_le_mul_of_nonneg_right hh (norm_nonneg u))
    simpa only [one_mul] using hm
  have mh₁ (u : CircleL2 T) : ‖circleMultiplyL2 T h₁ u‖ ≤ 2*‖u‖ :=
    (circle_multiply_l2_norm_le T h₁ u).trans (mul_le_mul_of_nonneg_right hh₁ (norm_nonneg u))
  have mh₂ (u : CircleL2 T) : ‖circleMultiplyL2 T h₂ u‖ ≤ 4*‖u‖ :=
    (circle_multiply_l2_norm_le T h₂ u).trans (mul_le_mul_of_nonneg_right hh₂ (norm_nonneg u))
  have hc : ‖circleFrequencyFactor T 1‖ ≤ 1 := by
    have hκpos : 0 < 2*Real.pi/T := by have := (Fact.out : 0 < T); positivity
    simpa only [circleFrequencyFactor, Int.cast_one, mul_one, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, abs_of_pos hκpos] using hκ
  have hscale (j : ℕ) (u : CircleL2 T) : ‖(circleFrequencyFactor T 1)^j • u‖ ≤ ‖u‖ := by
    rw [norm_smul, norm_pow]
    have hp := pow_le_pow_left₀ (norm_nonneg (circleFrequencyFactor T 1)) hc j
    simpa only [one_pow, one_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg u)
  have hraw (j : Fin 5) : ‖circleBlochCoefficient T h h₁ h₂ j f‖ ≤ 200*circleAngularH4Norm T f := by
    fin_cases j
    · change ‖circleBlochCoefficient T h h₁ h₂ 0 f‖ ≤ _
      rw [circle_bloch_zero_raw_apply]
      have h := norm_five_terms ((-4:ℂ) • (circleH4Jet T f).fourth)
        ((45:ℂ) • circleMultiplyL2 T h (circleH4Jet T f).second)
        ((75/2:ℂ) • circleMultiplyL2 T h₁ (circleH4Jet T f).first)
        ((42:ℂ) • (f:CircleL2 T)) ((15/2:ℂ) • circleMultiplyL2 T h₂ (f:CircleL2 T))
      conv at h => rhs; norm_num [norm_smul]
      linarith only [h, mh (circleH4Jet T f).second, mh₁ (circleH4Jet T f).first,
        mh₂ (f:CircleL2 T), hD, n0,n1,n2,n3,n4]
    · change ‖circleBlochCoefficient T h h₁ h₂ 1 f‖ ≤ _
      rw [circle_bloch_coefficient_one_apply]
      apply (show ‖circleFrequencyFactor T 1 • _‖ ≤ ‖_‖ from by simpa only [pow_one] using hscale 1 _).trans
      have h := norm_five_terms ((-16:ℂ) • (circleH4Jet T f).third)
        ((90:ℂ) • circleMultiplyL2 T h (circleH4Jet T f).first)
        ((75/2:ℂ) • circleMultiplyL2 T h₁ (f:CircleL2 T)) 0 0
      conv at h => rhs; norm_num [norm_smul]
      simp only [sub_zero, add_zero] at h
      linarith only [h, mh (circleH4Jet T f).first, mh₁ (f:CircleL2 T), hD,n0,n1,n2,n3,n4]
    · change ‖circleBlochCoefficient T h h₁ h₂ 2 f‖ ≤ _
      rw [circle_bloch_coefficient_two_apply]
      apply (hscale 2 _).trans
      have h := norm_five_terms ((-24:ℂ) • (circleH4Jet T f).second)
        ((45:ℂ) • circleMultiplyL2 T h (f:CircleL2 T)) 0 0 0
      conv at h => rhs; norm_num [norm_smul]
      simp only [sub_zero, add_zero] at h
      linarith only [h, mh (f:CircleL2 T),hD,n0,n1,n2,n3,n4]
    · change ‖circleBlochCoefficient T h h₁ h₂ 3 f‖ ≤ _
      rw [circle_bloch_coefficient_three_apply]
      apply (hscale 3 _).trans
      norm_num [norm_smul]
      linarith only [hD,n0,n1,n2,n3,n4]
    · change ‖circleBlochCoefficient T h h₁ h₂ 4 f‖ ≤ _
      rw [circle_bloch_coefficient_four_apply]
      apply (hscale 4 _).trans
      norm_num [norm_smul]
      linarith only [hD,n0,n1,n2,n3,n4]
  have hadj (j : Fin 5) : ‖circleBlochAdjointCoefficient T h h₁ h₂ j f‖ ≤ 200*circleAngularH4Norm T f := by
    fin_cases j
    · change ‖(-4:ℂ) • (circleH4Jet T f).fourth-
        (45:ℂ) • circleMultiplyL2 T h (circleH4Jet T f).second-
        (105/2:ℂ) • circleMultiplyL2 T h₁ (circleH4Jet T f).first-(42:ℂ) • (f:CircleL2 T)‖ ≤ _
      have h := norm_five_terms ((-4:ℂ) • (circleH4Jet T f).fourth)
        ((45:ℂ) • circleMultiplyL2 T h (circleH4Jet T f).second)
        ((105/2:ℂ) • circleMultiplyL2 T h₁ (circleH4Jet T f).first) ((42:ℂ) • (f:CircleL2 T)) 0
      conv at h => rhs; norm_num [norm_smul]
      simp only [add_zero] at h
      linarith only [h, mh (circleH4Jet T f).second, mh₁ (circleH4Jet T f).first,hD,n0,n1,n2,n3,n4]
    · change ‖circleBlochAdjointCoefficient T h h₁ h₂ 1 f‖ ≤ _
      rw [circle_bloch_adjoint_one_apply]
      apply (show ‖circleFrequencyFactor T 1 • _‖ ≤ ‖_‖ from by simpa only [pow_one] using hscale 1 _).trans
      have h := norm_five_terms ((-16:ℂ) • (circleH4Jet T f).third)
        ((90:ℂ) • circleMultiplyL2 T h (circleH4Jet T f).first)
        ((105/2:ℂ) • circleMultiplyL2 T h₁ (f:CircleL2 T)) 0 0
      conv at h => rhs; norm_num [norm_smul]
      simp only [sub_zero, add_zero] at h
      linarith only [h, mh (circleH4Jet T f).first, mh₁ (f:CircleL2 T),hD,n0,n1,n2,n3,n4]
    · change ‖circleBlochCoefficient T h h₁ h₂ 2 f‖ ≤ _
      exact hraw 2
    · change ‖circleBlochCoefficient T h h₁ h₂ 3 f‖ ≤ _
      exact hraw 3
    · change ‖circleBlochCoefficient T h h₁ h₂ 4 f‖ ≤ _
      exact hraw 4
  refine ⟨hraw, hadj, ?_⟩
  have heq : circleH4SymmetricOperator T h h₁ h₂ f = (1/2:ℂ) •
      (circleBlochCoefficient T h h₁ h₂ 0 f+circleBlochAdjointCoefficient T h h₁ h₂ 0 f) := by
    change _ = (1/2:ℂ) • (circleH4Operator T h h₁ h₂ f+circleH4FormalAdjoint T h h₁ f)
    rw [circle_h4_formal_adjoint_split T h h₁ h₂, circle_h4_operator_apply]
    unfold circleLinearL2Expression
    rw [← circle_h4_symmetric_operator_apply T h h₁ h₂ f]
    module
  rw [heq, norm_smul]
  norm_num
  have ht := norm_add_le (circleBlochCoefficient T h h₁ h₂ 0 f) (circleBlochAdjointCoefficient T h h₁ h₂ 0 f)
  linarith only [ht,hraw 0,hadj 0]

end Lemniscate
