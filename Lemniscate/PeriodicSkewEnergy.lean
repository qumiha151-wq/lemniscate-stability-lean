import Lemniscate.PeriodicProfileEnergy

/-! Multiplication by a real continuous coefficient is symmetric on L2.
The first-order correction from the symmetric expression to the linearized
expression has zero real energy on classical periodic functions. This does
not assert an unbounded-operator adjoint-domain theorem. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_multiply_l2_symmetric (h : C(AddCircle T, ℂ))
    (hh : ∀ x, conj (h x) = h x) (f g : CircleL2 T) :
    inner ℂ (circleMultiplyL2 T h f) g = inner ℂ f (circleMultiplyL2 T h g) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [circle_multiply_l2_ae T h f, circle_multiply_l2_ae T h g]
    with x hf hg
  simp only [RCLike.inner_apply', hf, hg, map_mul, hh x]
  ring

theorem circle_multiply_real_pairing (h : C(AddCircle T, ℂ))
    (hh : ∀ x, conj (h x) = h x) (f g : CircleL2 T) :
    (inner ℂ g (circleMultiplyL2 T h f)).re =
      (inner ℂ f (circleMultiplyL2 T h g)).re := by
  have he : conj (inner ℂ f (circleMultiplyL2 T h g)) =
      inner ℂ g (circleMultiplyL2 T h f) := by
    rw [inner_conj_symm, circle_multiply_l2_symmetric T h hh]
  have hr := congrArg Complex.re he
  simpa only [Complex.conj_re] using hr.symm

theorem circle_first_order_skew_energy (h h₁ f f₁ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hf : HasCircleDeriv T f f₁)
    (hreal : ∀ x, conj (h x) = h x) :
    (inner ℂ (circleContinuousL2 T f)
      (circleContinuousL2 T (h*f₁+(1/2:ℂ) • (h₁*f)))).re = 0 := by
  have hi := circle_classical_integration_by_parts T f f₁ (h*f)
    (h₁*f+h*f₁) hf (circle_deriv_mul T h h₁ f f₁ hh hf)
  have hl : circleContinuousL2 T (h₁*f+h*f₁) =
      circleContinuousL2 T (h₁*f)+circleContinuousL2 T (h*f₁) := by
    simp only [circleContinuousL2, map_add]
  rw [hl, inner_add_right] at hi
  have hr := congrArg Complex.re hi
  have hs := circle_multiply_real_pairing T h hreal
    (circleContinuousL2 T f) (circleContinuousL2 T f₁)
  rw [circle_multiply_l2_continuous, circle_multiply_l2_continuous] at hs
  simp only [Complex.neg_re, Complex.add_re] at hr
  have hl₂ : circleContinuousL2 T (h*f₁+(1/2:ℂ) • (h₁*f)) =
      circleContinuousL2 T (h*f₁)+(1/2:ℂ) • circleContinuousL2 T (h₁*f) := by
    simp only [circleContinuousL2, map_add, map_smul]
  rw [hl₂, inner_add_right, inner_smul_right]
  simp only [Complex.add_re, Complex.mul_re]
  norm_num
  linarith

end Lemniscate
