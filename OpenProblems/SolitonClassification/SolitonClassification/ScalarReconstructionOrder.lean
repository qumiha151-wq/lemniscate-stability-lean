import SolitonClassification.ScalarReconstructionJets
import SolitonClassification.ScalarReconstructionUniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic.IntervalCases

/-! A reconstruction frontier reached from a nonzero anchor has curvature
vanishing order at most three. A flat triple would give a zero solution of the
regular third-order equation, contradicting the anchor. -/

noncomputable section
open Set
open scoped ContDiff
namespace ClosedSimilarity.ScalarReconstruction

theorem finite_order_at_endpoint {k : ℝ → ℝ}
    (hk : ContDiff ℝ ∞ k) {a b : ℝ} (_hS : ScalarEquation k a b)
    (s₀ z : ℝ) (hanchor : k s₀ ≠ 0)
    (hdefect : ∀ x ∈ uIcc s₀ z, defect k a b s₀ x = 0) :
    ∃ m ≤ 3, (∀ j < m, iteratedDeriv j k z = 0) ∧ iteratedDeriv m k z ≠ 0 := by
  by_cases h0 : k z = 0
  · by_cases h1 : deriv k z = 0
    · by_cases h2 : deriv (deriv k) z = 0
      · have hb : b ≠ 0 := by
          intro hb
          have hk₁ := (contDiff_infty_iff_deriv.mp hk).2
          have hk₂ := (contDiff_infty_iff_deriv.mp hk₁).2
          have hzero := zero_jet_of_regular_ode_on_uIcc
            (s := z) (t := s₀) (k := k) (v := deriv k) (w := deriv (deriv k))
            (H := candidateSupport k a b s₀)
            hk.continuous hk₁.continuous hk₂.continuous
            (candidateSupport_smooth hk a b s₀).continuous
            (fun x _ => (hk.differentiable (by simp) x).hasDerivAt)
            (fun x _ => (hk₁.differentiable (by simp) x).hasDerivAt)
            (fun x hx => by
              have he := third_deriv_eq_of_defect_zero hk a b s₀ x
                (hdefect x (by simpa only [uIcc_comm] using hx))
              rw [hb, sub_zero] at he
              rw [hb, ← he]
              exact (hk₂.differentiable (by simp) x).hasDerivAt)
            h0 h1 h2
          exact hanchor hzero.1
        refine ⟨3, le_rfl, ?_, ?_⟩
        · intro j hj
          interval_cases j <;> simp [iteratedDeriv_succ, h0, h1, h2]
        · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
            third_deriv_ne_zero_at_curvature_zero hk a b s₀ z hb
              (hdefect z right_mem_uIcc) h0
      · refine ⟨2, by decide, ?_, ?_⟩
        · intro j hj
          interval_cases j <;> simp [iteratedDeriv_succ, h0, h1]
        · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h2
    · refine ⟨1, by decide, ?_, ?_⟩
      · intro j hj
        interval_cases j
        exact h0
      · simpa only [iteratedDeriv_one] using h1
  · exact ⟨0, by decide, fun j hj => (Nat.not_lt_zero j hj).elim, h0⟩

end ClosedSimilarity.ScalarReconstruction

#print axioms ClosedSimilarity.ScalarReconstruction.finite_order_at_endpoint

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`ClosedSimilarity.ScalarReconstruction).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
      checked := checked + 1
  logInfo m!"ScalarReconstructionOrder: audited {checked} declarations; standard axioms only."
