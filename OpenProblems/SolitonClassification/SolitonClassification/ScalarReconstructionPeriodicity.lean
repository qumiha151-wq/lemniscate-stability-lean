import SolitonClassification.ScalarReconstructionResidual
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Periodicity of the globally reconstructed support coefficient.
The global scalar identity is an explicit bridge input and is discharged
by ScalarReconstructionGlobal in the final curve reconstruction. -/
noncomputable section
open scoped ContDiff
namespace ClosedSimilarity.ScalarReconstruction

theorem periodic_deriv {k : ℝ → ℝ} {L : ℝ}
    (hper : Function.Periodic k L) : Function.Periodic (deriv k) L := by
  have he : (fun s => k (s+L)) = k := funext hper
  intro s
  rw [← deriv_comp_add_const, he]

theorem force_periodic {k : ℝ → ℝ} {L : ℝ}
    (hper : Function.Periodic k L) : Function.Periodic (force k) L := by
  intro s
  dsimp only [force]
  rw [periodic_deriv (periodic_deriv hper) s, hper s]

theorem numerator_periodic {k : ℝ → ℝ} {L : ℝ}
    (hper : Function.Periodic k L) (b : ℝ) :
    Function.Periodic (numerator k b) L := by
  intro s
  dsimp only [numerator]
  rw [periodic_deriv (force_periodic hper) s]

theorem supportDerivative_periodic {k : ℝ → ℝ} {L : ℝ}
    (hper : Function.Periodic k L) (a : ℝ) :
    Function.Periodic (supportDerivative k a) L := by
  intro s
  dsimp only [supportDerivative]
  rw [hper s, force_periodic hper s]

theorem candidateSupport_periodic_of_global_identity {k : ℝ → ℝ}
    (hk : ContDiff ℝ ∞ k) {a b L : ℝ} (hper : Function.Periodic k L)
    (s₀ : ℝ) (hanchor : k s₀ ≠ 0)
    (hglobal : ∀ s, numerator k b s = k s*candidateSupport k a b s₀ s) :
    Function.Periodic (candidateSupport k a b s₀) L := by
  let H : ℝ → ℝ := fun s => candidateSupport k a b s₀ (s+L)
  have hH : ∀ s, HasDerivAt H (supportDerivative k a s) s := by
    intro s
    have hd := (candidateSupport_hasDerivAt hk a b s₀ (s+L)).comp s
      ((hasDerivAt_id s).add_const L)
    simpa only [Function.comp_def, id_eq, mul_one, supportDerivative_periodic hper a s]
      using hd
  have hHanchor : numerator k b s₀ = k s₀*H s₀ := by
    have h := hglobal (s₀+L)
    rw [numerator_periodic hper b s₀, hper s₀] at h
    exact h
  have he := candidateSupport_unique hk a b s₀ hanchor H hH hHanchor
  intro s
  exact congrFun he s

end ClosedSimilarity.ScalarReconstruction

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`ClosedSimilarity.ScalarReconstruction).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext, `Classical.choice, `Quot.sound] : Array Name).contains axiomName do
          throwError "Scalar reconstruction periodicity audit failed: {name} depends on {axiomName}"
      count := count + 1
  logInfo m!"Scalar reconstruction periodicity audit passed for {count} declarations."
