import Lemniscate.PeriodicResolventSmoothing

/-! Quantitative control of the lower-order part composed with the principal
resolvent. Coefficients are arbitrary continuous complex functions. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

theorem circle_multiply_l2_opNorm_le (h : C(AddCircle T, ℂ)) :
    ‖circleMultiplyL2 T h‖ ≤ ‖h‖ :=
  ContinuousLinearMap.opNorm_le_bound (circleMultiplyL2 T h) (norm_nonneg _)
    (circle_multiply_l2_norm_le T h)

noncomputable def circleLowerResolvent (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p) : CircleL2 T →L[ℂ] CircleL2 T :=
  (-45:ℂ) • ((circleMultiplyL2 T h).comp (circlePrincipalSecond T p hp)) +
    (-75/2:ℂ) • ((circleMultiplyL2 T h₁).comp (circlePrincipalFirst T p hp)) +
    (-42:ℂ) • circlePrincipalResolvent T (p^2) (by nlinarith) +
    (15/2:ℂ) • ((circleMultiplyL2 T h₂).comp
      (circlePrincipalResolvent T (p^2) (by nlinarith)))

noncomputable def circleLowerBound (h h₁ h₂ : C(AddCircle T, ℂ)) : ℝ :=
  (45/4)*‖h‖ + (375/8)*‖h₁‖ + 42 + (15/2)*‖h₂‖

theorem circle_lower_bound_nonneg (h h₁ h₂ : C(AddCircle T, ℂ)) :
    0 ≤ circleLowerBound T h h₁ h₂ := by
  unfold circleLowerBound
  positivity

theorem circle_multiply_comp_norm_le (h : C(AddCircle T, ℂ))
    (R : CircleL2 T →L[ℂ] CircleL2 T) (C : ℝ) (hR : ‖R‖ ≤ C) :
    ‖(circleMultiplyL2 T h).comp R‖ ≤ ‖h‖*C :=
  ((circleMultiplyL2 T h).opNorm_comp_le R).trans
    (mul_le_mul (circle_multiply_l2_opNorm_le T h) hR (norm_nonneg _) (norm_nonneg _))

theorem circle_four_term_norm_le (R₀ R₁ R₂ R₃ : CircleL2 T →L[ℂ] CircleL2 T) :
    ‖(-45:ℂ) • R₀ + (-75/2:ℂ) • R₁ + (-42:ℂ) • R₂ + (15/2:ℂ) • R₃‖ ≤
      45*‖R₀‖ + (75/2)*‖R₁‖ + 42*‖R₂‖ + (15/2)*‖R₃‖ := by
  have hn₁ : ‖(-45:ℂ)‖ = (45:ℝ) := by norm_num
  have hn₂ : ‖(-75/2:ℂ)‖ = (75/2:ℝ) := by norm_num
  have hn₃ : ‖(-42:ℂ)‖ = (42:ℝ) := by norm_num
  have hn₄ : ‖(15/2:ℂ)‖ = (15/2:ℝ) := by norm_num
  calc
    _ ≤ ‖(-45:ℂ) • R₀‖ + ‖(-75/2:ℂ) • R₁‖ +
        ‖(-42:ℂ) • R₂‖ + ‖(15/2:ℂ) • R₃‖ :=
      norm_add₄_le
    _ = _ := by rw [norm_smul, norm_smul, norm_smul, norm_smul, hn₁, hn₂, hn₃, hn₄]

theorem circle_lower_resolvent_norm_le (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p) :
    ‖circleLowerResolvent T h h₁ h₂ p hp‖ ≤ circleLowerBound T h h₁ h₂ / p := by
  have hp' : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hm₂ : ‖(circleMultiplyL2 T h).comp (circlePrincipalSecond T p hp)‖ ≤
      ‖h‖*(1/(4*p)) :=
    circle_multiply_comp_norm_le T h _ _ (circle_principal_second_norm_le T p hp)
  have hm₁ : ‖(circleMultiplyL2 T h₁).comp (circlePrincipalFirst T p hp)‖ ≤
      ‖h₁‖*(5/(4*p)) :=
    circle_multiply_comp_norm_le T h₁ _ _ (circle_principal_first_norm_le T p hp)
  have hm₀ : ‖(circleMultiplyL2 T h₂).comp
      (circlePrincipalResolvent T (p^2) (by nlinarith))‖ ≤ ‖h₂‖*(1/p) :=
    circle_multiply_comp_norm_le T h₂ _ _ (circle_principal_resolvent_coarse_norm_le T p hp)
  have hr := circle_principal_resolvent_coarse_norm_le T p hp
  unfold circleLowerResolvent
  calc
    _ ≤ 45*‖(circleMultiplyL2 T h).comp (circlePrincipalSecond T p hp)‖ +
        (75/2)*‖(circleMultiplyL2 T h₁).comp (circlePrincipalFirst T p hp)‖ +
        42*‖circlePrincipalResolvent T (p^2) (by nlinarith)‖ +
        (15/2)*‖(circleMultiplyL2 T h₂).comp
          (circlePrincipalResolvent T (p^2) (by nlinarith))‖ :=
      circle_four_term_norm_le T _ _ _ _
    _ ≤ 45*(‖h‖*(1/(4*p))) + (75/2)*(‖h₁‖*(5/(4*p))) +
        42*(1/p) + (15/2)*(‖h₂‖*(1/p)) := by
      exact add_le_add (add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hm₂ (by norm_num))
          (mul_le_mul_of_nonneg_left hm₁ (by norm_num)))
        (mul_le_mul_of_nonneg_left hr (by norm_num)))
        (mul_le_mul_of_nonneg_left hm₀ (by norm_num))
    _ = circleLowerBound T h h₁ h₂ / p := by
      unfold circleLowerBound
      field_simp
      ring

noncomputable def circleResolventScale (h h₁ h₂ : C(AddCircle T, ℂ)) : ℝ :=
  2*circleLowerBound T h h₁ h₂+1

theorem circle_resolvent_scale_ge_one (h h₁ h₂ : C(AddCircle T, ℂ)) :
    1 ≤ circleResolventScale T h h₁ h₂ := by
  have := circle_lower_bound_nonneg T h h₁ h₂
  unfold circleResolventScale
  linarith

theorem circle_lower_resolvent_norm_lt_one (h h₁ h₂ : C(AddCircle T, ℂ)) :
    ‖circleLowerResolvent T h h₁ h₂ (circleResolventScale T h h₁ h₂)
      (circle_resolvent_scale_ge_one T h h₁ h₂)‖ < 1 := by
  apply (circle_lower_resolvent_norm_le T h h₁ h₂ _ _).trans_lt
  have hC := circle_lower_bound_nonneg T h h₁ h₂
  unfold circleResolventScale
  apply (div_lt_iff₀ (by positivity : 0 < 2*circleLowerBound T h h₁ h₂+1)).mpr
  linarith

noncomputable def circleFullShift (h h₁ h₂ : C(AddCircle T, ℂ)) (r : ℝ) :
    circleH4Domain T →ₗ[ℂ] CircleL2 T :=
  (r:ℂ) • (circleH4Domain T).subtype - circleH4Operator T h h₁ h₂

theorem circle_full_shift_principal (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p) (f : CircleL2 T) :
    circleFullShift T h h₁ h₂ (p^2)
      (circlePrincipalResolventH4 T (p^2) (by nlinarith) f) =
      f-circleLowerResolvent T h h₁ h₂ p hp f := by
  have he : circleFullShift T h h₁ h₂ (p^2)
      (circlePrincipalResolventH4 T (p^2) (by nlinarith) f) =
      circlePrincipalShift T (p^2)
        (circlePrincipalResolventH4 T (p^2) (by nlinarith) f) -
      circleLowerResolvent T h h₁ h₂ p hp f := by
    simp only [circleFullShift, LinearMap.sub_apply, LinearMap.smul_apply,
      Submodule.subtype_apply, circle_h4_operator_expanded,
      circleLowerResolvent, add_apply,
      ContinuousLinearMap.comp_apply, smul_apply]
    rw [circle_principal_first_eq_jet, circle_principal_second_eq_jet]
    change _ = ((p^2:ℝ):ℂ) • (circlePrincipalResolvent T (p^2) (by nlinarith) f) +
      (4:ℂ) • (circleH4Jet T
        (circlePrincipalResolventH4 T (p^2) (by nlinarith) f)).fourth - _
    dsimp only [circlePrincipalResolventH4]
    module
  rw [he, circle_principal_resolvent_right_inverse]

theorem circle_principal_resolvent_h4_left_inverse (r : ℝ) (hr : 0 < r)
    (f : circleH4Domain T) :
    circlePrincipalResolventH4 T r hr (circlePrincipalShift T r f) = f := by
  apply Subtype.ext
  exact circle_principal_resolvent_left_inverse T r hr f

theorem circle_full_shift_factorization (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p) (f : circleH4Domain T) :
    circleFullShift T h h₁ h₂ (p^2) f =
      (1-circleLowerResolvent T h h₁ h₂ p hp) (circlePrincipalShift T (p^2) f) := by
  have he := circle_full_shift_principal T h h₁ h₂ p hp (circlePrincipalShift T (p^2) f)
  rw [circle_principal_resolvent_h4_left_inverse] at he
  simpa only [sub_apply, one_apply_eq_self] using he

end Lemniscate
