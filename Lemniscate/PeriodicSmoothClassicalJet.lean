import Lemniscate.PeriodicClassicalFourier
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! A smooth periodic function supplies its complete classical circle jet. -/
noncomputable section
namespace Lemniscate
open Complex
open scoped ContDiff

/-- Every iterated derivative of a periodic function has the same period. -/
theorem periodic_iterated_deriv (T : ℝ) (f : ℝ → ℂ)
    (hp : Function.Periodic f T) (j : ℕ) :
    Function.Periodic (iteratedDeriv j f) T := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using hp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    intro x
    exact (deriv_comp_add_const (iteratedDeriv j f) T x).symm.trans
      (congrArg (fun g : ℝ → ℂ => deriv g x) (funext ih))

/-- Every smooth periodic function, including a smooth initial normal
height, has a full sequence of genuine continuous circle derivatives. -/
theorem periodic_smooth_classical_jet (T : ℝ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f T) :
    ∃ F : ℕ → C(AddCircle T,ℂ),
      (∀ j : ℕ, ∀ x : ℝ, F j (x:AddCircle T)=iteratedDeriv j f x) ∧
      ∀ j : ℕ, HasCircleDeriv T (F j) (F (j+1)) := by
  have horder (j : ℕ) : (j : WithTop ℕ∞)<(∞ : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)
  let F : ℕ → C(AddCircle T,ℂ) := fun j =>
    ⟨(periodic_iterated_deriv T f hp j).lift,(hf.continuous_iteratedDeriv j (horder j).le).quotient_lift _⟩
  refine ⟨F,fun _ _ => rfl,?_⟩
  intro j x
  change HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j+1) f x) x
  rw [iteratedDeriv_succ]
  exact (hf.differentiable_iteratedDeriv j (horder j) x).hasDerivAt

end Lemniscate
