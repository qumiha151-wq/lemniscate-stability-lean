import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.NormNum
import Lean.Util.CollectAxioms

/-! Actual partial derivatives on the open time/parameter plane.
Schwarz symmetry is derived from C2 regularity of the actual map.
No mixed-partial equality is a hypothesis. -/

noncomputable section
open scoped ContDiff

namespace LengthGrowth.ActualFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def partialTime (f : ℝ × ℝ → E) (x : ℝ × ℝ) : E :=
  fderiv ℝ f x (1, 0)

def partialSpace (f : ℝ × ℝ → E) (x : ℝ × ℝ) : E :=
  fderiv ℝ f x (0, 1)

theorem deriv_time_eq_partialTime {f : ℝ × ℝ → E} {x : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f x) :
    deriv (fun t => f (t, x.2)) x.1 = partialTime f x := by
  exact (hf.hasFDerivAt.comp_hasDerivAt x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))).deriv

theorem deriv_space_eq_partialSpace {f : ℝ × ℝ → E} {x : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f x) :
    deriv (fun u => f (x.1, u)) x.2 = partialSpace f x := by
  exact (hf.hasFDerivAt.comp_hasDerivAt x.2
    ((hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2))).deriv

theorem fderiv_apply_fixed {c : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] E}
    {x : ℝ × ℝ} (hc : DifferentiableAt ℝ c x) (v w : ℝ × ℝ) :
    fderiv ℝ (fun y => c y v) x w = fderiv ℝ c x w v := by
  rw [fderiv_clm_apply hc (differentiableAt_const v)]
  simp

theorem actual_partials_commute {f : ℝ × ℝ → E} {x : ℝ × ℝ}
    (hf : ContDiffAt ℝ 2 f x) :
    partialTime (partialSpace f) x = partialSpace (partialTime f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  change fderiv ℝ (fun y => fderiv ℝ f y (0, 1)) x (1, 0) =
    fderiv ℝ (fun y => fderiv ℝ f y (1, 0)) x (0, 1)
  rw [fderiv_apply_fixed hd, fderiv_apply_fixed hd]
  exact (hf.isSymmSndFDerivAt (by norm_num)).eq (1, 0) (0, 1)

end LengthGrowth.ActualFlow

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for n in #[`LengthGrowth.ActualFlow.deriv_time_eq_partialTime,
      `LengthGrowth.ActualFlow.deriv_space_eq_partialSpace,
      `LengthGrowth.ActualFlow.actual_partials_commute] do
    for a in (← collectAxioms n) do
      unless allowed.contains a do throwError "Unexpected axiom {a} in {n}"
  logInfo "Actual mixed partials: standard axioms only."
