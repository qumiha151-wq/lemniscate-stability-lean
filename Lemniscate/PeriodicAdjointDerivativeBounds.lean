import Lemniscate.PeriodicProfileBounds

/-! The formal-adjoint equation controls the fourth weak derivative. Together
with second-order residual control, this gives all derivatives in actual L2. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_adjoint_fourth_norm_le (h h₁ : C(AddCircle T, ℂ)) (f : circleH4Domain T) :
    4*‖(circleH4Jet T f).fourth‖ ≤ ‖circleH4FormalAdjoint T h h₁ f‖+
      45*‖h‖*‖(circleH4Jet T f).second‖+
      (105/2:ℝ)*‖h₁‖*‖(circleH4Jet T f).first‖+42*‖(f : CircleL2 T)‖ := by
  have heq : (-4:ℂ) • (circleH4Jet T f).fourth =
      circleH4FormalAdjoint T h h₁ f+(45:ℂ) • circleMultiplyL2 T h (circleH4Jet T f).second+
      (105/2:ℂ) • circleMultiplyL2 T h₁ (circleH4Jet T f).first+(42:ℂ) • (f : CircleL2 T) := by
    change (-4:ℂ) • (circleH4Jet T f).fourth =
      ((-4:ℂ) • (circleH4Jet T f).fourth-
        (45:ℂ) • circleMultiplyL2 T h (circleH4Jet T f).second-
        (105/2:ℂ) • circleMultiplyL2 T h₁ (circleH4Jet T f).first-
        (42:ℂ) • (f : CircleL2 T)) + _ + _ + _
    module
  have ht1 := norm_add_le (circleH4FormalAdjoint T h h₁ f)
    ((45:ℂ) • circleMultiplyL2 T h (circleH4Jet T f).second)
  have ht2 := norm_add_le
    (circleH4FormalAdjoint T h h₁ f+(45:ℂ) • circleMultiplyL2 T h (circleH4Jet T f).second)
    ((105/2:ℂ) • circleMultiplyL2 T h₁ (circleH4Jet T f).first)
  have ht3 := norm_add_le
    (circleH4FormalAdjoint T h h₁ f+(45:ℂ) • circleMultiplyL2 T h (circleH4Jet T f).second+
      (105/2:ℂ) • circleMultiplyL2 T h₁ (circleH4Jet T f).first) ((42:ℂ) • (f : CircleL2 T))
  have hn := congrArg norm heq
  have hm1 := circle_multiply_l2_norm_le T h₁ (circleH4Jet T f).first
  have hm2 := circle_multiply_l2_norm_le T h (circleH4Jet T f).second
  norm_num [norm_smul] at ht1 ht2 ht3 hn
  nlinarith

theorem circle_profile_coefficient_norms (q p : C(AddCircle T, ℂ))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x) :
    ‖q^2‖ ≤ 1 ∧ ‖(2:ℂ) • (q*p)‖ ≤ 2 := by
  have hnorm := circle_profile_uniform_norm T q p he hqreal hpreal
  constructor
  · calc
      _ ≤ ‖q‖^2 := norm_pow_le q 2
      _ ≤ 1^2 := pow_le_pow_left₀ (norm_nonneg _) hnorm.1 2
      _ = _ := by norm_num
  · have hm : ‖q*p‖ ≤ 1 := by
      calc
        _ ≤ ‖q‖*‖p‖ := norm_mul_le q p
        _ ≤ 1*1 := mul_le_mul hnorm.1 hnorm.2 (norm_nonneg _) (by norm_num)
        _ = _ := by norm_num
    norm_num [norm_smul]
    linarith

theorem paper_adjoint_fourth_norm_le (q p : C(AddCircle T, ℂ))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (f : circleH4Domain T) :
    4*‖(circleH4Jet T f).fourth‖ ≤ ‖circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) f‖+
      45*‖(circleH4Jet T f).second‖+105*‖(circleH4Jet T f).first‖+42*‖(f : CircleL2 T)‖ := by
  have hb := circle_adjoint_fourth_norm_le T (q^2) ((2:ℂ) • (q*p)) f
  have hc := circle_profile_coefficient_norms T q p he hqreal hpreal
  have hm2 := mul_le_mul_of_nonneg_right hc.1 (norm_nonneg (circleH4Jet T f).second)
  have hm1 := mul_le_mul_of_nonneg_right hc.2 (norm_nonneg (circleH4Jet T f).first)
  nlinarith

theorem paper_adjoint_all_derivative_bounds (q p : C(AddCircle T, ℂ))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (f : circleH4Domain T) (R : ℝ) (hR : 0 ≤ R)
    (hres : ‖circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) f‖ ≤ R)
    (hmass : ‖(f : CircleL2 T)‖ ≤ R/75)
    (hsecond : ‖(circleH4Jet T f).second‖^2 ≤ R^2/15) :
    ‖(circleH4Jet T f).first‖ ≤ R ∧ ‖(circleH4Jet T f).second‖ ≤ R ∧
      ‖(circleH4Jet T f).third‖ ≤ 7*R ∧ ‖(circleH4Jet T f).fourth‖ ≤ 38*R := by
  have hsecond1 : ‖(circleH4Jet T f).second‖ ≤ R := by
    nlinarith [norm_nonneg (circleH4Jet T f).second, sq_nonneg R]
  have hfirst2 := circle_weak_derivative_norm_sq_product T (f : CircleL2 T)
    (circleH4Jet T f).first (circleH4Jet T f).second
    (circleH4Jet T f).hfirst (circleH4Jet T f).hsecond
  have hfirst : ‖(circleH4Jet T f).first‖ ≤ R := by
    have hm := mul_le_mul hmass hsecond1 (norm_nonneg _) (by positivity : 0 ≤ R/75)
    nlinarith [norm_nonneg (circleH4Jet T f).first, sq_nonneg R]
  have hfourth0 := paper_adjoint_fourth_norm_le T q p he hqreal hpreal f
  have hfourth : ‖(circleH4Jet T f).fourth‖ ≤ 38*R := by linarith
  have hthird2 := circle_weak_derivative_norm_sq_product T (circleH4Jet T f).second
    (circleH4Jet T f).third (circleH4Jet T f).fourth
    (circleH4Jet T f).hthird (circleH4Jet T f).hfourth
  have hm := mul_le_mul hsecond1 hfourth (norm_nonneg _) hR
  have hthird : ‖(circleH4Jet T f).third‖ ≤ 7*R := by
    nlinarith [norm_nonneg (circleH4Jet T f).third, sq_nonneg R]
  exact ⟨hfirst, hsecond1, hthird, hfourth⟩

end Lemniscate
