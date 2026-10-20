import Lemniscate.PeriodicH4Operator
import Mathlib.Tactic.Module

/-! Green identities on the actual H4 domain and the formal adjoint expression.
The final identity is an inclusion in the adjoint relation; equality of the
maximal Hilbert adjoint domain with H4 still requires a regularity argument. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_h4_fourth_green (f g : circleH4Domain T) :
    inner ℂ (circleH4Jet T f).fourth (g : CircleL2 T) =
      inner ℂ (f : CircleL2 T) (circleH4Jet T g).fourth := by
  calc
    _ = -inner ℂ (circleH4Jet T f).third (circleH4Jet T g).first :=
      circle_weak_integration_by_parts T _ _ _ _
        (circleH4Jet T f).hfourth (circleH4Jet T g).hfirst
    _ = inner ℂ (circleH4Jet T f).second (circleH4Jet T g).second := by
      rw [circle_weak_integration_by_parts T _ _ _ _
        (circleH4Jet T f).hthird (circleH4Jet T g).hsecond, neg_neg]
    _ = -inner ℂ (circleH4Jet T f).first (circleH4Jet T g).third :=
      circle_weak_integration_by_parts T _ _ _ _
        (circleH4Jet T f).hsecond (circleH4Jet T g).hthird
    _ = _ := by
      rw [circle_weak_integration_by_parts T _ _ _ _
        (circleH4Jet T f).hfirst (circleH4Jet T g).hfourth, neg_neg]

theorem circle_h4_divergence_green (h h₁ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (f g : circleH4Domain T) :
    inner ℂ (circleMultiplyL2 T h₁ (circleH4Jet T f).first+
      circleMultiplyL2 T h (circleH4Jet T f).second) (g : CircleL2 T) =
      inner ℂ (f : CircleL2 T) (circleMultiplyL2 T h₁ (circleH4Jet T g).first+
        circleMultiplyL2 T h (circleH4Jet T g).second) := by
  have hp (u : circleH4Domain T) : HasWeakCircleDeriv T
      (circleMultiplyL2 T h (circleH4Jet T u).first)
      (circleMultiplyL2 T h₁ (circleH4Jet T u).first+
        circleMultiplyL2 T h (circleH4Jet T u).second) := by
    simpa only [add_comm] using circle_real_multiply_weak_deriv T h h₁ hh hreal h₁real
      _ _ (circleH4Jet T u).hsecond
  have hf := circle_weak_integration_by_parts T _ _ _ _ (hp f) (circleH4Jet T g).hfirst
  have hg := circle_weak_integration_by_parts T _ _ _ _ (circleH4Jet T f).hfirst (hp g)
  rw [hf, circle_multiply_l2_symmetric T h hreal, hg, neg_neg]

theorem circle_h4_symmetric_green (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) (f g : circleH4Domain T) :
    inner ℂ (circleH4SymmetricOperator T h h₁ h₂ f) (g : CircleL2 T) =
      inner ℂ (f : CircleL2 T) (circleH4SymmetricOperator T h h₁ h₂ g) := by
  have hd := circle_h4_divergence_green T h h₁ hh hreal h₁real f g
  simp only [inner_add_left, inner_add_right] at hd
  rw [circle_h4_symmetric_operator_apply, circle_h4_symmetric_operator_apply]
  unfold circleSymmetricL2Expression
  simp only [inner_add_left, inner_sub_left, inner_smul_left,
    inner_add_right, inner_sub_right, inner_smul_right]
  rw [circle_h4_fourth_green, hd, circle_multiply_l2_symmetric T h₂ h₂real]
  norm_num [map_ofNat]

theorem circle_weak_skew_green (h h₁ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (f f₁ g g₁ : CircleL2 T)
    (hf : HasWeakCircleDeriv T f f₁) (hg : HasWeakCircleDeriv T g g₁) :
    inner ℂ (circleMultiplyL2 T h f₁+(1/2:ℂ) • circleMultiplyL2 T h₁ f) g =
      -inner ℂ f (circleMultiplyL2 T h g₁+(1/2:ℂ) • circleMultiplyL2 T h₁ g) := by
  have hi := circle_weak_integration_by_parts T _ _ g g₁
    (circle_real_multiply_weak_deriv T h h₁ hh hreal h₁real f f₁ hf) hg
  rw [inner_add_left, circle_multiply_l2_symmetric T h hreal,
    circle_multiply_l2_symmetric T h₁ h₁real,
    circle_multiply_l2_symmetric T h hreal] at hi
  simp only [inner_add_left, inner_smul_left, inner_add_right, inner_smul_right,
    circle_multiply_l2_symmetric T h hreal, circle_multiply_l2_symmetric T h₁ h₁real]
  norm_num [map_ofNat]
  rw [eq_sub_of_add_eq hi]
  ring

/-- The expression -4D^4-45hD^2-(105/2)h'D-42 on the H4 domain.
It is called formal adjoint until equality of maximal domains is established. -/
noncomputable def circleH4FormalAdjoint (h h₁ : C(AddCircle T, ℂ)) :
    circleH4Domain T →ₗ[ℂ] CircleL2 T :=
  (-4:ℂ) • circleH4Derivative T 3 -
    (45:ℂ) • (circleMultiplyL2 T h).toLinearMap.comp (circleH4Derivative T 1) -
    (105/2:ℂ) • (circleMultiplyL2 T h₁).toLinearMap.comp (circleH4Derivative T 0) -
    (42:ℂ) • (circleH4Domain T).subtype

theorem circle_h4_formal_adjoint_split (h h₁ h₂ : C(AddCircle T, ℂ))
    (f : circleH4Domain T) :
    circleH4FormalAdjoint T h h₁ f = circleH4SymmetricOperator T h h₁ h₂ f -
      (15/2:ℂ) • (circleMultiplyL2 T h₁ (circleH4Jet T f).first+
        (1/2:ℂ) • circleMultiplyL2 T h₂ (f : CircleL2 T)) := by
  change (-4:ℂ) • (circleH4Jet T f).fourth -
    (45:ℂ) • circleMultiplyL2 T h (circleH4Jet T f).second -
    (105/2:ℂ) • circleMultiplyL2 T h₁ (circleH4Jet T f).first -
    (42:ℂ) • (f : CircleL2 T) = _
  rw [circle_h4_symmetric_operator_apply]
  unfold circleSymmetricL2Expression
  module

theorem circle_h4_formal_adjoint_green (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) (f g : circleH4Domain T) :
    inner ℂ (circleH4Operator T h h₁ h₂ f) (g : CircleL2 T) =
      inner ℂ (f : CircleL2 T) (circleH4FormalAdjoint T h h₁ g) := by
  have hk := circle_weak_skew_green T h₁ h₂ hh₁ h₁real h₂real
    (f : CircleL2 T) (circleH4Jet T f).first (g : CircleL2 T) (circleH4Jet T g).first
    (circleH4Jet T f).hfirst (circleH4Jet T g).hfirst
  rw [circle_h4_formal_adjoint_split T h h₁ h₂]
  change inner ℂ (circleH4SymmetricOperator T h h₁ h₂ f +
    (15/2:ℂ) • (circleMultiplyL2 T h₁ (circleH4Jet T f).first+
      (1/2:ℂ) • circleMultiplyL2 T h₂ (f : CircleL2 T))) (g : CircleL2 T) = _
  rw [inner_add_left, inner_smul_left, inner_sub_right, inner_smul_right,
    circle_h4_symmetric_green T h h₁ h₂ hh hreal h₁real h₂real, hk]
  norm_num [map_ofNat]
  ring

end Lemniscate
