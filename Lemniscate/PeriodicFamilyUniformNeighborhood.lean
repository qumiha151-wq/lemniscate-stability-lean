import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Field.Periodic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith

noncomputable section
namespace Lemniscate

open Set Filter
open scoped Topology

/-- Joint continuity of two periodic families gives uniform spatial closeness
on a relative parameter neighborhood. The comparison functions need not be
periodic. -/
theorem periodic_family_uniform_neighborhood
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (C : Set P) (p₀ : P) (hp₀ : p₀ ∈ C)
    (Γ V : P × ℝ → ℂ)
    (hΓ : ContinuousOn Γ (C ×ˢ (univ : Set ℝ)))
    (hV : ContinuousOn V (C ×ˢ (univ : Set ℝ)))
    (L : ℝ) (hL : 0 < L)
    (hΓper : ∀ p ∈ C, Function.Periodic (fun s => Γ (p,s)) L)
    (hVper : ∀ p ∈ C, Function.Periodic (fun s => V (p,s)) L)
    (β T : ℝ → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hΓbase : ∀ s, ‖Γ (p₀,s) - β s‖ ≤ δ / 2)
    (hVbase : ∀ s, ‖V (p₀,s) - T s‖ ≤ δ / 2) :
    ∃ r > 0, ∀ p ∈ C, dist p p₀ < r → ∀ s,
      ‖Γ (p,s) - β s‖ < δ ∧ ‖V (p,s) - T s‖ < δ := by
  have hpair : ContinuousOn (fun z : P × ℝ => (Γ z,V z))
      (C ×ˢ Icc 0 L) :=
    (hΓ.prodMk hV).mono (fun _ hz => ⟨hz.1,mem_univ _⟩)
  obtain ⟨A,hA,hclose⟩ := isCompact_Icc.mem_uniformity_of_prod
    (f := fun p s => (Γ (p,s),V (p,s)))
    (by simpa only [Function.uncurry] using! hpair) hp₀
    (Metric.dist_mem_uniformity (half_pos hδ))
  obtain ⟨r,hr,hrA⟩ := Metric.mem_nhdsWithin_iff.mp hA
  refine ⟨r,hr,?_⟩
  intro p hp hdist s
  have hpA : p ∈ A := hrA ⟨hdist,hp⟩
  have hper : Function.Periodic
      (fun x => (Γ (p,x) - Γ (p₀,x),V (p,x) - V (p₀,x))) L := by
    intro x
    exact Prod.ext
      (by
        change Γ (p,x+L)-Γ (p₀,x+L)=Γ (p,x)-Γ (p₀,x)
        exact congrArg₂ (·-·) (hΓper p hp x) (hΓper p₀ hp₀ x))
      (by
        change V (p,x+L)-V (p₀,x+L)=V (p,x)-V (p₀,x)
        exact congrArg₂ (·-·) (hVper p hp x) (hVper p₀ hp₀ x))
  obtain ⟨x,hx,heq⟩ := hper.exists_mem_Ico₀ hL s
  have hc : dist (Γ (p,x),V (p,x)) (Γ (p₀,x),V (p₀,x)) < δ / 2 :=
    hclose p hpA x ⟨hx.1,hx.2.le⟩
  have hc' : ‖Γ (p,x) - Γ (p₀,x)‖ < δ / 2 ∧
      ‖V (p,x) - V (p₀,x)‖ < δ / 2 := by
    rw [Prod.dist_eq] at hc
    exact ⟨by simpa only [dist_eq_norm] using (max_lt_iff.mp hc).1,
      by simpa only [dist_eq_norm] using (max_lt_iff.mp hc).2⟩
  have hΓsmall : ‖Γ (p,s) - Γ (p₀,s)‖ < δ / 2 := by
    rw [show Γ (p,s) - Γ (p₀,s) = Γ (p,x) - Γ (p₀,x) from
      congrArg Prod.fst heq]
    exact hc'.1
  have hVsmall : ‖V (p,s) - V (p₀,s)‖ < δ / 2 := by
    rw [show V (p,s) - V (p₀,s) = V (p,x) - V (p₀,x) from
      congrArg Prod.snd heq]
    exact hc'.2
  have hΓtriangle : ‖Γ (p,s) - β s‖ ≤
      ‖Γ (p,s) - Γ (p₀,s)‖ + ‖Γ (p₀,s) - β s‖ := by
    simpa only [dist_eq_norm] using dist_triangle (Γ (p,s)) (Γ (p₀,s)) (β s)
  have hVtriangle : ‖V (p,s) - T s‖ ≤
      ‖V (p,s) - V (p₀,s)‖ + ‖V (p₀,s) - T s‖ := by
    simpa only [dist_eq_norm] using dist_triangle (V (p,s)) (V (p₀,s)) (T s)
  constructor
  · linarith only [hΓtriangle,hΓsmall,hΓbase s]
  · linarith only [hVtriangle,hVsmall,hVbase s]

end Lemniscate
