import SolitonClassification.ScalarReconstructionCurve
import SolitonClassification.ScalarReconstructionNecessity

/-! Equivalence of the actual scalar equation and the periodic support ODE for
a given smooth nonzero periodic curvature. This statement does not enumerate
periodic solutions or remove the independent integer holonomy requirement for
position closure. -/
noncomputable section
open scoped ContDiff
namespace ClosedSimilarity.ScalarReconstruction

def reconstructedSupportProfile {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    {a b L : ℝ} (hS : ScalarEquation k a b) (hper : Function.Periodic k L)
    (s₀ : ℝ) (hanchor : k s₀≠0) (hden : a^2+b^2≠0) :
    PeriodicSupportProfile a b L where
  k := k
  v := deriv k
  p := normalCoefficient k a b s₀
  q := tangentCoefficient k a b s₀
  dk s := (hk.differentiable (by simp) s).hasDerivAt
  dv s := by
    have hk₁ := (contDiff_infty_iff_deriv.mp hk).2
    have hf := force_eq_coefficients k a b s₀ s hden
    have he : deriv (deriv k) s =
        -(k s)^3/2-a*normalCoefficient k a b s₀ s-b*tangentCoefficient k a b s₀ s := by
      dsimp only [force] at hf
      linarith
    rw [← he]
    exact (hk₁.differentiable (by simp) s).hasDerivAt
  dp := normalCoefficient_hasDerivAt hk hS s₀ hanchor
  dq := tangentCoefficient_hasDerivAt hk hS s₀ hanchor hden
  periodic_k := hper
  periodic_v := periodic_deriv hper
  periodic_p := (coefficients_periodic hk hS hper s₀ hanchor).1
  periodic_q := (coefficients_periodic hk hS hper s₀ hanchor).2

/-- A precise reduction, rather than a classification of periodic ODE orbits.
No zero-set, quotient-extension, or support-identity premise is needed. -/
theorem scalarEquation_iff_exists_periodicSupportProfile {k : ℝ → ℝ}
    (hk : ContDiff ℝ ∞ k) {a b L : ℝ} (hper : Function.Periodic k L)
    (hnonzero : ∃ s₀, k s₀≠0) (hden : a^2+b^2≠0) :
    ScalarEquation k a b ↔ ∃ z : PeriodicSupportProfile a b L, z.k=k := by
  constructor
  · intro hS
    obtain ⟨s₀,hanchor⟩ := hnonzero
    exact ⟨reconstructedSupportProfile hk hS hper s₀ hanchor hden,rfl⟩
  · rintro ⟨z,hz⟩
    rw [← hz]
    exact scalarEquation_of_periodicSupportProfile z

end ClosedSimilarity.ScalarReconstruction

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`ClosedSimilarity).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Scalar equivalence audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Scalar equivalence audit passed for {count} declarations."
