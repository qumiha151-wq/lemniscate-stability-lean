import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Lean.Util.CollectAxioms

/-! Smoothness of actual integral curves follows from the smooth vector field.
This module proves the bootstrap rather than assuming a smooth solution. -/
noncomputable section
open scoped ContDiff
namespace OpenTranslator

theorem smooth_integral_curve_of_smooth_field
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : E → E} (hV : ContDiff ℝ ∞ V) {x : ℝ → E}
    (hx : ∀ t, HasDerivAt x (V (x t)) t) : ContDiff ℝ ∞ x := by
  have hd : Differentiable ℝ x := fun t => (hx t).differentiableAt
  have he : deriv x = V ∘ x := funext fun t => (hx t).deriv
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hd.continuous
  | succ n ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨hd, by simp, ?_⟩
    rw [he]
    exact (contDiff_infty.mp hV n).comp ih

end OpenTranslator
#print axioms OpenTranslator.smooth_integral_curve_of_smooth_field
