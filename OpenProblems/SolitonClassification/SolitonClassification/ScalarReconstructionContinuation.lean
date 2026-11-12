import SolitonClassification.ScalarReconstructionZeros
import Mathlib.Topology.Order.IntermediateValue
import Lean.Util.CollectAxioms

/-! Continuous induction for a smooth Wronskian-zero pair. This intermediate
lemma exposes its finite-order premise; the scalar ODE supplies that premise
in the final reconstruction theorem. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace ClosedSimilarity.ScalarReconstruction

theorem wronskian_zero_global_of_order_on_zero_segments (f g : ℝ → ℝ) (s₀ : ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hwr : ∀ x, g x*deriv f x-deriv g x*f x=0)
    (hfanchor : f s₀=0) (hganchor : g s₀≠0)
    (horder : ∀ z, (∀ x∈uIcc s₀ z, f x=0) →
      ∃ m, (∀ j<m, iteratedDeriv j g z=0) ∧ iteratedDeriv m g z≠0) :
    ∀ s, f s=0 := by
  intro s
  have hclosed : IsClosed {x | f x=0} := isClosed_eq hf.continuous continuous_const
  have hjanchor : ∀ j≤0, iteratedDeriv j f s₀=0 := by
    intro j hj
    have hj0 : j=0 := Nat.eq_zero_of_le_zero hj
    simpa only [hj0,iteratedDeriv_zero] using hfanchor
  rcases le_total s₀ s with hs | hs
  · have hcoverage := (hclosed.inter (isClosed_Icc (a := s₀) (b := s))).Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hfanchor (by
      intro z hz hp
      by_cases hsz : s₀=z
      · subst z
        exact zero_right_of_finite_order f g s₀ 0 hf hg hwr hjanchor
          (fun j hj => (Nat.not_lt_zero j hj).elim) hganchor
      · have hsz' : s₀<z := lt_of_le_of_ne hz.1 hsz
        have hprefix : ∀ x∈Icc s₀ z, f x=0 := fun x hx => hp hx
        obtain ⟨m, hm0, hmn⟩ := horder z (by
          simpa only [uIcc_of_le hz.1] using hprefix)
        exact zero_right_of_finite_order f g z m hf hg hwr
          (fun j _ => zero_jets_at_right_endpoint f s₀ z hf hsz' hprefix j) hm0 hmn)
    exact hcoverage (right_mem_Icc.mpr hs)
  · have hclosed' : IsClosed (OrderDual.ofDual ⁻¹' ({x : ℝ | f x=0} ∩ Icc s s₀)) :=
      hclosed.inter isClosed_Icc
    rw [preimage_inter, ← Icc_toDual] at hclosed'
    have hcoverage := hclosed'.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset
      hfanchor (by
      intro z hz hp
      change ∀ᶠ x in 𝓝[<] (OrderDual.ofDual z), f x=0
      have hzs : OrderDual.ofDual z≤s₀ := hz.1
      have hprefix : ∀ x∈Icc (OrderDual.ofDual z) s₀, f x=0 :=
        fun x hx => hp (a := OrderDual.toDual x) ⟨hx.2,hx.1⟩
      by_cases hsz : s₀=OrderDual.ofDual z
      · rw [← hsz]
        exact zero_left_of_finite_order f g s₀ 0 hf hg hwr hjanchor
          (fun j hj => (Nat.not_lt_zero j hj).elim) hganchor
      · have hzs' : OrderDual.ofDual z<s₀ := lt_of_le_of_ne hzs (Ne.symm hsz)
        obtain ⟨m, hm0, hmn⟩ := horder (OrderDual.ofDual z) (by
          simpa only [uIcc_of_ge hzs] using hprefix)
        exact zero_left_of_finite_order f g (OrderDual.ofDual z) m hf hg hwr
          (fun j _ => zero_jets_at_left_endpoint f (OrderDual.ofDual z) s₀ hf hzs' hprefix j) hm0 hmn)
    exact hcoverage ⟨hs,le_rfl⟩

end ClosedSimilarity.ScalarReconstruction

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`ClosedSimilarity.ScalarReconstruction).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Scalar continuation audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Scalar continuation audit passed for {count} declarations."
