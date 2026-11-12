import OpenTranslators.Geometry
import Mathlib.Tactic.LinearCombination

/-! Frenet identities derived solely from actual smooth unit-speed coordinates.
There is no angle, curvature field, or Frenet equation among the input data. -/

namespace OpenTranslator.Immersion
noncomputable section
open Set
open scoped ContDiff

def curvature (x y : ℝ → ℝ) : ℝ → ℝ := TranslatorGeometry.signedCurvature x y

variable {x y : ℝ → ℝ}
variable (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
variable (hunit : ∀ s, (deriv x s)^2+(deriv y s)^2=1)

include hx hy in
theorem curvature_smooth : ContDiff ℝ ∞ (curvature x y) := by
  have hx₁ := (contDiff_infty_iff_deriv.mp hx).2
  have hy₁ := (contDiff_infty_iff_deriv.mp hy).2
  have hx₂ := (contDiff_infty_iff_deriv.mp hx₁).2
  have hy₂ := (contDiff_infty_iff_deriv.mp hy₁).2
  exact (hx₁.mul hy₂).sub (hy₁.mul hx₂)

include hx hy hunit in
theorem tangent_acceleration_orthogonal (s : ℝ) :
    deriv x s * deriv (deriv x) s + deriv y s * deriv (deriv y) s = 0 := by
  have hdx := ((contDiff_infty_iff_deriv.mp hx).2.differentiable (by simp) s).hasDerivAt
  have hdy := ((contDiff_infty_iff_deriv.mp hy).2.differentiable (by simp) s).hasDerivAt
  have hd := (hdx.pow 2).add (hdy.pow 2)
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at hd
  change HasDerivAt (fun u => (deriv x u)^2+(deriv y u)^2)
    (2*deriv x s*deriv (deriv x) s+2*deriv y s*deriv (deriv y) s) s at hd
  have he : (fun u => (deriv x u)^2+(deriv y u)^2) = fun _ => (1:ℝ) := funext hunit
  rw [he] at hd
  have hh := hd.unique (hasDerivAt_const s (1:ℝ))
  linarith

include hx hy hunit in
theorem frenet_x (s : ℝ) : deriv (deriv x) s = -curvature x y s * deriv y s := by
  have ho := tangent_acceleration_orthogonal hx hy hunit s
  have hu := hunit s
  dsimp [curvature, TranslatorGeometry.signedCurvature]
  linear_combination -deriv (deriv x) s * hu + deriv x s * ho

include hx hy hunit in
theorem frenet_y (s : ℝ) : deriv (deriv y) s = curvature x y s * deriv x s := by
  have ho := tangent_acceleration_orthogonal hx hy hunit s
  have hu := hunit s
  dsimp [curvature, TranslatorGeometry.signedCurvature]
  linear_combination -deriv (deriv y) s * hu + deriv y s * ho

end
end OpenTranslator.Immersion

#print axioms OpenTranslator.Immersion.frenet_x
