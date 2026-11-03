import Lemniscate.PeriodicMultiplication
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Banach-algebra operations used by the rational normal-graph equation.
The inverse evaluation identity requires the coefficient function to be a unit.
Coefficient multiplication is bundled jointly, including the L2 argument. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ENNReal

theorem continuous_map_ring_inverse_apply {X : Type*} [TopologicalSpace X]
    (a : C(X, ℂ)) (ha : IsUnit a) (x : X) :
    Ring.inverse a x = (a x)⁻¹ := by
  have hx : a x ≠ 0 := (ContinuousMap.isUnit_iff_forall_ne_zero a).mp ha x
  apply mul_left_cancel₀ hx
  have h := congrArg (fun b : C(X, ℂ) => b x) (Ring.mul_inverse_cancel a ha)
  change a x*Ring.inverse a x = 1 at h
  rw [h,mul_inv_cancel₀ hx]

variable (T : ℝ) [Fact (0 < T)]

def circleCoefficientMultiplyL2 :
    C(AddCircle T, ℂ) →L[ℂ] CircleL2 T →L[ℂ] CircleL2 T :=
  ((ContinuousLinearMap.mul ℂ ℂ).holderL AddCircle.haarAddCircle ∞ 2 2).comp
    (ContinuousMap.toLp ∞ AddCircle.haarAddCircle ℂ)

@[simp] theorem circle_coefficient_multiply_l2_apply
    (a : C(AddCircle T, ℂ)) (f : CircleL2 T) :
    circleCoefficientMultiplyL2 T a f = circleMultiplyL2 T a f := rfl

theorem circle_coefficient_multiply_l2_contDiff :
    ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun p : C(AddCircle T, ℂ) × CircleL2 T => circleMultiplyL2 T p.1 p.2) := by
  exact (circleCoefficientMultiplyL2 T).isBoundedBilinearMap.contDiff

end Lemniscate
