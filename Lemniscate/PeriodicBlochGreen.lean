import Lemniscate.PeriodicBlochParity
import Lemniscate.PeriodicFormalAdjoint

/-! Integration by parts for the positive-degree Bloch coefficients. These
identities move derivatives from the high-frequency input to a fixed test
function, so the later coupling estimate only needs L2 Parseval. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_h4_first_green (f g : circleH4Domain T) :
    inner ℂ (circleH4Jet T f).first (g : CircleL2 T) =
      -inner ℂ (f : CircleL2 T) (circleH4Jet T g).first :=
  circle_weak_integration_by_parts T _ _ _ _ (circleH4Jet T f).hfirst (circleH4Jet T g).hfirst

theorem circle_h4_second_green (f g : circleH4Domain T) :
    inner ℂ (circleH4Jet T f).second (g : CircleL2 T) =
      inner ℂ (f : CircleL2 T) (circleH4Jet T g).second := by
  rw [circle_weak_integration_by_parts T _ _ _ _
    (circleH4Jet T f).hsecond (circleH4Jet T g).hfirst,
    circle_weak_integration_by_parts T _ _ _ _
    (circleH4Jet T f).hfirst (circleH4Jet T g).hsecond, neg_neg]

theorem circle_h4_third_green (f g : circleH4Domain T) :
    inner ℂ (circleH4Jet T f).third (g : CircleL2 T) =
      -inner ℂ (f : CircleL2 T) (circleH4Jet T g).third := by
  rw [circle_weak_integration_by_parts T _ _ _ _
    (circleH4Jet T f).hthird (circleH4Jet T g).hfirst,
    circle_weak_integration_by_parts T _ _ _ _
    (circleH4Jet T f).hsecond (circleH4Jet T g).hsecond,
    circle_weak_integration_by_parts T _ _ _ _
    (circleH4Jet T f).hfirst (circleH4Jet T g).hthird]
  simp only [neg_neg]

theorem circle_h4_multiply_first_green (h h₁ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (f g : circleH4Domain T) :
    inner ℂ (circleMultiplyL2 T h (circleH4Jet T f).first) (g : CircleL2 T) =
      -inner ℂ (f : CircleL2 T) (circleMultiplyL2 T h (circleH4Jet T g).first)-
        inner ℂ (f : CircleL2 T) (circleMultiplyL2 T h₁ (g : CircleL2 T)) := by
  have hi := circle_weak_skew_green T h h₁ hh hreal h₁real
    (f : CircleL2 T) (circleH4Jet T f).first
    (g : CircleL2 T) (circleH4Jet T g).first
    (circleH4Jet T f).hfirst (circleH4Jet T g).hfirst
  simp only [inner_add_left, inner_smul_left, inner_add_right, inner_smul_right,
    circle_multiply_l2_symmetric T h₁ h₁real] at hi
  norm_num [map_ofNat] at hi
  linear_combination hi

noncomputable def circleBlochAdjointCoefficient (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 5) : circleH4Domain T →ₗ[ℂ] CircleL2 T :=
  ![circleH4FormalAdjoint T h h₁,
    circleBlochCoefficient T h h₁ h₂ 1-
      (15*circleFrequencyFactor T 1) •
        (circleMultiplyL2 T h₁).toLinearMap.comp (circleH4Domain T).subtype,
    circleBlochCoefficient T h h₁ h₂ 2,
    circleBlochCoefficient T h h₁ h₂ 3,
    circleBlochCoefficient T h h₁ h₂ 4] j

theorem circle_bloch_coefficient_green (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) (j : Fin 5) (f g : circleH4Domain T) :
    inner ℂ (circleBlochCoefficient T h h₁ h₂ j f) (g : CircleL2 T) =
      inner ℂ (f : CircleL2 T) (circleBlochAdjointCoefficient T h h₁ h₂ j g) := by
  fin_cases j
  · change inner ℂ (circleH4Operator T h h₁ h₂ f) (g : CircleL2 T) =
      inner ℂ (f : CircleL2 T) (circleH4FormalAdjoint T h h₁ g)
    exact circle_h4_formal_adjoint_green T h h₁ h₂ hh hh₁ hreal h₁real h₂real f g
  · change inner ℂ (circleBlochCoefficient T h h₁ h₂ 1 f) (g : CircleL2 T) =
      inner ℂ (f : CircleL2 T) (circleBlochCoefficient T h h₁ h₂ 1 g-
        (15*circleFrequencyFactor T 1) • circleMultiplyL2 T h₁ (g : CircleL2 T))
    rw [circle_bloch_coefficient_one_apply, circle_bloch_coefficient_one_apply]
    simp only [inner_smul_left, inner_sub_left, inner_smul_right, inner_sub_right,
      circle_frequency_factor_conj, circle_h4_third_green,
      circle_h4_multiply_first_green T h h₁ hh hreal h₁real,
      circle_multiply_l2_symmetric T h₁ h₁real]
    norm_num [map_ofNat]
    ring
  · change inner ℂ (circleBlochCoefficient T h h₁ h₂ 2 f) (g : CircleL2 T) =
      inner ℂ (f : CircleL2 T) (circleBlochCoefficient T h h₁ h₂ 2 g)
    rw [circle_bloch_coefficient_two_apply, circle_bloch_coefficient_two_apply]
    simp only [inner_smul_left, inner_sub_left, inner_smul_right, inner_sub_right,
      map_pow, circle_frequency_factor_conj, neg_sq, circle_h4_second_green,
      circle_multiply_l2_symmetric T h hreal]
    norm_num [map_ofNat]
  · change inner ℂ (circleBlochCoefficient T h h₁ h₂ 3 f) (g : CircleL2 T) =
      inner ℂ (f : CircleL2 T) (circleBlochCoefficient T h h₁ h₂ 3 g)
    rw [circle_bloch_coefficient_three_apply, circle_bloch_coefficient_three_apply]
    simp only [inner_smul_left, inner_smul_right, map_pow,
      circle_frequency_factor_conj, circle_h4_first_green]
    norm_num [map_ofNat]
    ring
  · change inner ℂ (circleBlochCoefficient T h h₁ h₂ 4 f) (g : CircleL2 T) =
      inner ℂ (f : CircleL2 T) (circleBlochCoefficient T h h₁ h₂ 4 g)
    rw [circle_bloch_coefficient_four_apply, circle_bloch_coefficient_four_apply]
    simp only [inner_smul_left, inner_smul_right, map_pow, circle_frequency_factor_conj,
      show (-circleFrequencyFactor T 1)^4 = (circleFrequencyFactor T 1)^4 by ring]
    norm_num [map_ofNat]

end Lemniscate
