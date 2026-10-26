import Lemniscate.PeriodicAdjointResidual

/-! Bounds needed to lift an adjoint residual estimate to H4. These are
proved for actual circle L2 multiplication and weak derivatives. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_profile_pointwise_norm (q p : C(AddCircle T, ℂ))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (x : AddCircle T) : ‖q x‖ ≤ 1 ∧ ‖p x‖ ≤ 1 := by
  obtain ⟨a, ha⟩ := Complex.conj_eq_iff_real.mp (hqreal x)
  obtain ⟨b, hb⟩ := Complex.conj_eq_iff_real.mp (hpreal x)
  have hec := he x
  rw [ha, hb] at hec
  have her : 2*b^2+a^4 = (1:ℝ) := by exact_mod_cast hec
  have ha2 : a^2 ≤ 1 := by nlinarith [sq_nonneg b, sq_nonneg (a^2-1)]
  have hb2 : b^2 ≤ 1 := by nlinarith [sq_nonneg (a^2)]
  rw [ha, hb, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith

theorem circle_profile_uniform_norm (q p : C(AddCircle T, ℂ))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x) :
    ‖q‖ ≤ 1 ∧ ‖p‖ ≤ 1 := by
  constructor
  · exact (ContinuousMap.norm_le q (by norm_num : (0:ℝ) ≤ 1)).mpr
      (fun x => (circle_profile_pointwise_norm T q p he hqreal hpreal x).1)
  · exact (ContinuousMap.norm_le p (by norm_num : (0:ℝ) ≤ 1)).mpr
      (fun x => (circle_profile_pointwise_norm T q p he hqreal hpreal x).2)

theorem circle_multiply_l2_mul (h k : C(AddCircle T, ℂ)) (f : CircleL2 T) :
    circleMultiplyL2 T (h*k) f = circleMultiplyL2 T h (circleMultiplyL2 T k f) := by
  apply Lp.ext
  filter_upwards [circle_multiply_l2_ae T (h*k) f,
    circle_multiply_l2_ae T h (circleMultiplyL2 T k f), circle_multiply_l2_ae T k f]
    with x hhk hh hk
  rw [hhk, hh, hk]
  change (h x*k x)*f x = h x*(k x*f x)
  ring

theorem circle_real_square_pairing (h : C(AddCircle T, ℂ))
    (hreal : ∀ x, conj (h x) = h x) (f : CircleL2 T) :
    (inner ℂ f (circleMultiplyL2 T (h^2) f)).re = ‖circleMultiplyL2 T h f‖^2 := by
  rw [pow_two, circle_multiply_l2_mul, ← circle_multiply_l2_symmetric T h hreal]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

theorem paper_h2_energy_squared_norms (q : C(AddCircle T, ℂ))
    (hqreal : ∀ x, conj (q x) = q x) (f f₁ f₂ : CircleL2 T) :
    paperH2Energy T q f f₁ f₂ = -4*‖f₂‖^2+45*‖circleMultiplyL2 T q f₁‖^2-
      (153/4:ℝ)*‖f‖^2-(45/4:ℝ)*‖circleMultiplyL2 T (q^2) f‖^2 := by
  have hq2 := circle_real_square_pairing T q hqreal f₁
  have hq4 : (inner ℂ f (circleMultiplyL2 T (q^4) f)).re =
      ‖circleMultiplyL2 T (q^2) f‖^2 := by
    rw [show q^4 = (q^2)^2 by ring]
    apply circle_real_square_pairing T (q^2) _ f
    intro x
    change conj ((q x)^2) = (q x)^2
    simp only [map_pow, hqreal]
  unfold paperH2Energy
  simp only [inner_self_eq_norm_sq_to_K]
  norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re, hq2, hq4]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]

theorem paper_h2_energy_garding (q : C(AddCircle T, ℂ))
    (hqreal : ∀ x, conj (q x) = q x) (hqnorm : ‖q‖ ≤ 1)
    (f f₁ f₂ : CircleL2 T) (hf : HasWeakCircleDeriv T f f₁)
    (hf₁ : HasWeakCircleDeriv T f₁ f₂) :
    paperH2Energy T q f f₁ f₂ ≤ -2*‖f₂‖^2+(1719/8:ℝ)*‖f‖^2 := by
  have hm : ‖circleMultiplyL2 T q f₁‖ ≤ ‖f₁‖ := by
    calc
      _ ≤ ‖q‖*‖f₁‖ := circle_multiply_l2_norm_le T q f₁
      _ ≤ 1*‖f₁‖ := mul_le_mul_of_nonneg_right hqnorm (norm_nonneg _)
      _ = _ := one_mul _
  have hm2 : ‖circleMultiplyL2 T q f₁‖^2 ≤ ‖f₁‖^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hm 2
  have hd := circle_weak_derivative_norm_sq_product T f f₁ f₂ hf hf₁
  apply garding_interpolation
  rw [paper_h2_energy_squared_norms T q hqreal]
  nlinarith [sq_nonneg ‖circleMultiplyL2 T (q^2) f‖]

theorem paper_h4_operator_garding (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (f : circleH4Domain T) :
    (inner ℂ (f : CircleL2 T)
      (circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) f)).re ≤
        -2*‖(circleH4Jet T f).second‖^2+(1719/8:ℝ)*‖(f : CircleL2 T)‖^2 := by
  have h0real : ∀ x, conj ((q^2 : C(AddCircle T, ℂ)) x) = (q^2 : C(AddCircle T, ℂ)) x := by
    intro x
    change conj ((q x)^2) = (q x)^2
    simp only [map_pow, hqreal]
  have h1real : ∀ x, conj (((2:ℂ) • (q*p)) x) = ((2:ℂ) • (q*p)) x := by
    intro x
    change conj (2*(q x*p x)) = 2*(q x*p x)
    simp only [map_mul, map_ofNat, hqreal, hpreal]
  have h2real : ∀ x, conj ((1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) x) =
      (1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) x := by
    intro x
    change conj (1-3*(q x)^4) = 1-3*(q x)^4
    simp only [map_sub, map_mul, map_one, map_ofNat, map_pow, hqreal]
  rw [circle_h4_operator_energy T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
    (circle_profile_square_deriv T q p hq) (circle_profile_square_second T q p hq hp he)
    h0real h1real h2real, circle_h2_energy_profile]
  exact paper_h2_energy_garding T q hqreal (circle_profile_uniform_norm T q p he hqreal hpreal).1
    _ _ _ (circleH4Jet T f).hfirst (circleH4Jet T f).hsecond

end Lemniscate
