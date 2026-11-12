import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Connected.Clopen
import Lean.Util.CollectAxioms

/-! Global uniqueness for actual integral curves of a locally Lipschitz field.
The proof propagates the local ODE uniqueness theorem through the connected
time axis. No globally uniform Lipschitz constant is assumed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace OpenTranslator

theorem unique_global_of_locallyLipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : E → E} (hV : LocallyLipschitz V) {f g : ℝ → E}
    (hf : ∀ t, HasDerivAt f (V (f t)) t)
    (hg : ∀ t, HasDerivAt g (V (g t)) t)
    {t₀ : ℝ} (heq : f t₀ = g t₀) : f = g := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun t => (hf t).continuousAt
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt
  let S : Set ℝ := {t | f t = g t}
  have hc : IsClosed S := isClosed_eq hfc hgc
  have ho : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    obtain ⟨K, U, hU, hLip⟩ := hV (f t)
    have hUf : ∀ᶠ r in 𝓝 t, f r ∈ U := (hf t).continuousAt.tendsto.eventually hU
    have hUg : ∀ᶠ r in 𝓝 t, g r ∈ U := by
      have hU' : U ∈ 𝓝 (g t) := by simpa only [show f t = g t from ht] using hU
      exact (hg t).continuousAt.tendsto.eventually hU'
    have he : f =ᶠ[𝓝 t] g := ODE_solution_unique_of_eventually
      (v := fun _ => V) (s := fun _ => U) (Filter.Eventually.of_forall fun _ => hLip)
      (hUf.mono fun r hr => ⟨hf r, hr⟩)
      (hUg.mono fun r hr => ⟨hg r, hr⟩) ht
    exact he
  have hu : S = univ := (show IsClopen S from ⟨hc, ho⟩).eq_univ ⟨t₀, heq⟩
  funext t
  have ht : t ∈ S := by rw [hu]; exact mem_univ t
  exact ht

end OpenTranslator
#print axioms OpenTranslator.unique_global_of_locallyLipschitz
