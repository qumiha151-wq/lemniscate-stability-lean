import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Lean.Util.CollectAxioms

/-! Integration by parts for actual derivatives of periodic fields.
The endpoint cancellation follows from periodicity, and integrability follows
from smoothness on the compact parameter interval. -/

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace LengthGrowth.ActualFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem periodic_inner_integration_by_parts {f g : ℝ → E} {P : ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : Function.Periodic f P) (hgp : Function.Periodic g P) :
    (∫ u in 0..P, inner ℝ (f u) (deriv g u)) =
      -(∫ u in 0..P, inner ℝ (deriv f u) (g u)) := by
  have hf' := (contDiff_infty_iff_deriv.mp hf).2.continuous
  have hg' := (contDiff_infty_iff_deriv.mp hg).2.continuous
  have hi₁ : IntervalIntegrable (fun u => inner ℝ (deriv f u) (g u)) volume 0 P :=
    (hf'.inner hg.continuous).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (fun u => inner ℝ (f u) (deriv g u)) volume 0 P :=
    (hf.continuous.inner hg').intervalIntegrable _ _
  have hd (u : ℝ) : HasDerivAt (fun x => inner ℝ (f x) (g x))
      (inner ℝ (deriv f u) (g u) + inner ℝ (f u) (deriv g u)) u :=
    by simpa only [add_comm] using
      ((hf.differentiable (by simp) u).hasDerivAt).inner ℝ
        ((hg.differentiable (by simp) u).hasDerivAt)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hd u) (hi₁.add hi₂)
  have hfe : f P = f 0 := by simpa using hfp 0
  have hge : g P = g 0 := by simpa using hgp 0
  rw [hfe, hge, sub_self, intervalIntegral.integral_add hi₁ hi₂] at h
  linarith

theorem periodic_mul_integration_by_parts {f g : ℝ → ℝ} {P : ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : Function.Periodic f P) (hgp : Function.Periodic g P) :
    (∫ u in 0..P, f u * deriv g u) = -(∫ u in 0..P, deriv f u * g u) := by
  simpa only [Real.inner_apply] using
    periodic_inner_integration_by_parts hf hg hfp hgp

end LengthGrowth.ActualFlow

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for n in #[`LengthGrowth.ActualFlow.periodic_inner_integration_by_parts,
      `LengthGrowth.ActualFlow.periodic_mul_integration_by_parts] do
    for a in (← collectAxioms n) do
      unless allowed.contains a do throwError "Unexpected axiom {a} in {n}"
  logInfo "Periodic integration by parts: standard axioms only."
