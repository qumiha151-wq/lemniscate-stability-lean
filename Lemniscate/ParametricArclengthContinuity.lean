import Lemniscate.ParametricOrderIsoContinuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Joint continuity of arclength coordinates and their inverses follows
from joint continuity of the actual curve velocity. No time derivative,
higher spatial regularity or extension of the parameter space is needed. -/
namespace Lemniscate
open MeasureTheory

/-- A family of increasing arclength coordinates and its inverse depend
jointly continuously on any topological parameter when the actual
velocity field is jointly continuous. -/
theorem parametric_arclength_continuity
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    (v : X × ℝ → E) (hv : Continuous v)
    (e : X → (ℝ ≃o ℝ))
    (he : ∀ x : X, ∀ u : ℝ, e x u=∫ s in (0:ℝ)..u, ‖v (x,s)‖) :
    Continuous (fun p : X × ℝ => e p.1 p.2) ∧
      Continuous (fun p : X × ℝ => (e p.1).symm p.2) := by
  have hspeed : Continuous (Function.uncurry (fun x : X => fun s : ℝ => ‖v (x,s)‖)) :=
    hv.norm
  have hIntegral := intervalIntegral.continuous_parametric_primitive_of_continuous
    (μ := (volume : Measure ℝ)) (a₀ := (0:ℝ)) hspeed
  have hforward : Continuous (fun p : X × ℝ => e p.1 p.2) := by
    simpa only [he] using hIntegral
  exact ⟨hforward,parametric_order_iso_inverse_continuous e hforward⟩

end Lemniscate
