import SolitonClassification.ScalarReconstructionResidual
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith

/-! Actual third-order curvature identities used at a reconstruction frontier.
These identities do not assume or prove the global vanishing of the defect. -/
noncomputable section
open scoped ContDiff
namespace ClosedSimilarity.ScalarReconstruction

theorem force_hasDerivAt_third {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) (s : ℝ) :
    HasDerivAt (force k)
      (deriv (deriv (deriv k)) s + (3/2:ℝ)*k s^2*deriv k s) s := by
  have hk₁ := (contDiff_infty_iff_deriv.mp hk).2
  have hk₂ := (contDiff_infty_iff_deriv.mp hk₁).2
  have hd := (hk.differentiable (by simp) s).hasDerivAt
  convert ((hk₂.differentiable (by simp) s).hasDerivAt).add
    ((hd.pow 3).div_const 2) using 1 <;> first | rfl | ring

theorem numerator_eq_third {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) (b s : ℝ) :
    numerator k b s = deriv (deriv (deriv k)) s +
      (3/2:ℝ)*k s^2*deriv k s + b := by
  dsimp only [numerator]
  rw [(force_hasDerivAt_third hk s).deriv]

theorem third_deriv_eq_of_defect_zero {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    (a b s₀ s : ℝ) (hz : defect k a b s₀ s = 0) :
    deriv (deriv (deriv k)) s =
      k s*candidateSupport k a b s₀ s - b - (3/2:ℝ)*k s^2*deriv k s := by
  dsimp only [defect] at hz
  rw [numerator_eq_third hk] at hz
  linarith

theorem third_deriv_at_curvature_zero {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    (a b s₀ s : ℝ) (hz : defect k a b s₀ s = 0) (hks : k s = 0) :
    deriv (deriv (deriv k)) s = -b := by
  simpa [hks] using
    third_deriv_eq_of_defect_zero hk a b s₀ s hz

theorem third_deriv_ne_zero_at_curvature_zero {k : ℝ → ℝ}
    (hk : ContDiff ℝ ∞ k) (a b s₀ s : ℝ) (hb : b ≠ 0)
    (hz : defect k a b s₀ s = 0) (hks : k s = 0) :
    deriv (deriv (deriv k)) s ≠ 0 := by
  rw [third_deriv_at_curvature_zero hk a b s₀ s hz hks]
  exact neg_ne_zero.mpr hb

end ClosedSimilarity.ScalarReconstruction

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`ClosedSimilarity.ScalarReconstruction).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext, `Classical.choice, `Quot.sound] : Array Name).contains axiomName do
          throwError "Scalar reconstruction jets audit failed: {name} depends on {axiomName}"
      count := count + 1
  logInfo m!"Scalar reconstruction jets audit passed for {count} declarations."
