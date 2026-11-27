import SolitonClassification.RamifiedBoundedDeck

noncomputable section
open Complex Set Filter
open scoped Topology
namespace ClosedSimilarity.RamifiedBounded

/-- A bounded curvature branch on a finite ramified cover has a holomorphic
filling invariant under every deck transformation. No bound is assumed on
the differentiated curvature or on the support components. -/
theorem bounded_curvature_deck {m:ℕ} {a b:ℂ} {k v F h:ℂ→ℂ} (hm:0<m)
    (bound : ∃ C:ℝ,∀ᶠ w in 𝓝[≠] (0:ℂ),‖k w‖≤C)
    (law : ∀ᶠ w in 𝓝[≠] (0:ℂ),Laws m a b k v F h w) :
    ∃ K:ℂ→ℂ,AnalyticAt ℂ K 0 ∧ k=ᶠ[𝓝[≠] 0] K ∧
      ∀η:ℂ,η^m=1 → (fun z=>K (η*z))=ᶠ[𝓝 0] K := by
  have fk := fills_of_bounded (law.mono (fun _ l=>l.1.differentiableAt)) bound
  obtain ⟨r,ar,er⟩ := fk
  rcases ar.eventually_eq_zero_or_eventually_ne_zero with zero | ne
  · refine ⟨fun _=>0,analyticAt_const,er.trans (zero.filter_mono nhdsWithin_le_nhds),?_⟩
    exact fun _ _=>EventuallyEq.rfl
  · have nk : ∀ᶠ w in 𝓝[≠] (0:ℂ),k w≠0 := by
      filter_upwards [er,ne] with w ew nw
      rwa [ew]
    have fk' : Fills k := ⟨r,ar,er⟩
    obtain ⟨fv,fF,fh⟩ := stress_fills hm fk' nk law
    obtain ⟨Y,ey,-⟩ := filled_state fk' fv fF fh law
    exact ⟨Y.k,Y.ak,ey,fun _ he=>Y.curvature_deck hm.ne' he⟩

#print axioms bounded_curvature_deck
end ClosedSimilarity.RamifiedBounded
