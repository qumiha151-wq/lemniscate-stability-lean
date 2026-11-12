import SolitonClassification.ScalarReconstructionContinuation
import SolitonClassification.ScalarReconstructionOrder

/-! Global reconstruction of the support variable directly from the smooth
fourth-order scalar equation, including arbitrary curvature zero sets. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace ClosedSimilarity.ScalarReconstruction

/-- No zero-set regularity or global quotient extension is assumed. The scalar
equation and a nonzero anchor force the integral candidate's defect to vanish
through all curvature zeros. -/
theorem defect_eq_zero_global {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    {a b : ℝ} (hS : ScalarEquation k a b) (s₀ : ℝ) (hanchor : k s₀≠0) :
    ∀ s, defect k a b s₀ s=0 := by
  apply wronskian_zero_global_of_order_on_zero_segments
    (defect k a b s₀) k s₀ (defect_smooth hk a b s₀) hk
    (defect_wronskian hk hS s₀) (defect_at_anchor k a b s₀ hanchor) hanchor
  intro z hz
  obtain ⟨m, _, hm0, hmn⟩ := finite_order_at_endpoint hk hS s₀ z hanchor hz
  exact ⟨m,hm0,hmn⟩

theorem candidateSupport_eq_quotient_global {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    {a b : ℝ} (hS : ScalarEquation k a b) (s₀ : ℝ) (hanchor : k s₀≠0) (s : ℝ) :
    numerator k b s=k s*candidateSupport k a b s₀ s := by
  exact sub_eq_zero.mp (defect_eq_zero_global hk hS s₀ hanchor s)

theorem exists_smooth_support_of_scalar_equation {k : ℝ → ℝ}
    (hk : ContDiff ℝ ∞ k) {a b : ℝ} (hS : ScalarEquation k a b)
    (hnonzero : ∃ s₀, k s₀≠0) :
    ∃ H : ℝ → ℝ, ContDiff ℝ ∞ H ∧
      (∀ s, HasDerivAt H (a-k s*force k s) s) ∧
      (∀ s, numerator k b s=k s*H s) := by
  obtain ⟨s₀,hs₀⟩ := hnonzero
  refine ⟨candidateSupport k a b s₀,candidateSupport_smooth hk a b s₀,?_,?_⟩
  · exact candidateSupport_hasDerivAt hk a b s₀
  · exact candidateSupport_eq_quotient_global hk hS s₀ hs₀

end ClosedSimilarity.ScalarReconstruction

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`ClosedSimilarity.ScalarReconstruction).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Scalar global audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Scalar global audit passed for {count} declarations."
