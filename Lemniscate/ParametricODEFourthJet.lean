import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic.FinCases

/-! The first four actual derivatives of an ODE solution depend
continuously on an arbitrary topological parameter. -/
noncomputable section
namespace Lemniscate
open Set

/-- Three spatial derivatives of the vector field suffice for joint
continuity of the actual fourth derivative jet of its trajectories.
No differentiation in the topological parameter and no symmetry of the
higher derivative maps is assumed. -/
theorem parametric_ode_fourth_jet
    {K E : Type*} [TopologicalSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (O : Set E)
    (V₀ : K → E → E) (V₁ : K → E → (E →L[ℝ] E))
    (V₂ : K → E → (E →L[ℝ] (E →L[ℝ] E)))
    (V₃ : K → E → (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E))))
    (hV₀ : ContinuousOn (fun p : K × E => V₀ p.1 p.2) (univ ×ˢ O))
    (hV₁ : ContinuousOn (fun p : K × E => V₁ p.1 p.2) (univ ×ˢ O))
    (hV₂ : ContinuousOn (fun p : K × E => V₂ p.1 p.2) (univ ×ˢ O))
    (hV₃ : ContinuousOn (fun p : K × E => V₃ p.1 p.2) (univ ×ˢ O))
    (hD₀ : ∀ k x, x ∈ O → HasFDerivAt (V₀ k) (V₁ k x) x)
    (hD₁ : ∀ k x, x ∈ O → HasFDerivAt (V₁ k) (V₂ k x) x)
    (hD₂ : ∀ k x, x ∈ O → HasFDerivAt (V₂ k) (V₃ k x) x)
    (y : K → ℝ → E) (hy : Continuous (fun p : K × ℝ => y p.1 p.2))
    (hO : ∀ k s, y k s ∈ O)
    (hODE : ∀ k s, HasDerivAt (y k) (V₀ k (y k s)) s) :
    Continuous (fun p : K × ℝ =>
      fun j : Fin 5 => iteratedDeriv j.val (y p.1) p.2) := by
  let A : K → ℝ → E := fun k s => V₀ k (y k s)
  let B : K → ℝ → (E →L[ℝ] E) := fun k s => V₁ k (y k s)
  let C : K → ℝ → (E →L[ℝ] (E →L[ℝ] E)) := fun k s => V₂ k (y k s)
  let D : K → ℝ → (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E))) := fun k s => V₃ k (y k s)
  let J₂ : K → ℝ → E := fun k s => B k s (A k s)
  let J₃ : K → ℝ → E := fun k s =>
    C k s (A k s) (A k s)+B k s (J₂ k s)
  let J₄ : K → ℝ → E := fun k s =>
    (((D k s (A k s)) (A k s)+C k s (J₂ k s)) (A k s)+
        C k s (A k s) (J₂ k s))+
      (C k s (A k s) (J₂ k s)+B k s (J₃ k s))
  have hA (k : K) (s : ℝ) : HasDerivAt (A k) (J₂ k s) s :=
    (hD₀ k (y k s) (hO k s)).comp_hasDerivAt s (hODE k s)
  have hB (k : K) (s : ℝ) : HasDerivAt (B k) (C k s (A k s)) s :=
    (hD₁ k (y k s) (hO k s)).comp_hasDerivAt s (hODE k s)
  have hC (k : K) (s : ℝ) : HasDerivAt (C k) (D k s (A k s)) s := by
    have hc := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := E)
      (E := E →L[ℝ] (E →L[ℝ] E)) s (hD₂ k (y k s) (hO k s)) (hODE k s)
    simpa only [C,D,A,Function.comp_def] using! hc
  have hJ₂ (k : K) (s : ℝ) : HasDerivAt (J₂ k) (J₃ k s) s :=
    (hB k s).clm_apply (𝕜 := ℝ) (hA k s)
  have hJ₃ (k : K) (s : ℝ) : HasDerivAt (J₃ k) (J₄ k s) s :=
    (((hC k s).clm_apply (𝕜 := ℝ) (hA k s)).clm_apply (𝕜 := ℝ) (hA k s)).add
      ((hB k s).clm_apply (𝕜 := ℝ) (hJ₂ k s))
  have hjet₁ (k : K) : iteratedDeriv 1 (y k) = A k := by
    rw [iteratedDeriv_succ,iteratedDeriv_zero]
    funext s
    exact (hODE k s).deriv
  have hjet₂ (k : K) : iteratedDeriv 2 (y k) = J₂ k := by
    rw [iteratedDeriv_succ,hjet₁ k]
    funext s
    exact (hA k s).deriv
  have hjet₃ (k : K) : iteratedDeriv 3 (y k) = J₃ k := by
    rw [iteratedDeriv_succ,hjet₂ k]
    funext s
    exact (hJ₂ k s).deriv
  have hjet₄ (k : K) : iteratedDeriv 4 (y k) = J₄ k := by
    rw [iteratedDeriv_succ,hjet₃ k]
    funext s
    exact (hJ₃ k s).deriv
  have hgraph : Continuous (fun p : K × ℝ => (p.1,y p.1 p.2)) :=
    continuous_fst.prodMk hy
  have hgraphMem (p : K × ℝ) : (p.1,y p.1 p.2) ∈ (univ : Set K) ×ˢ O :=
    ⟨mem_univ _,hO p.1 p.2⟩
  have hAc : Continuous (fun p : K × ℝ => A p.1 p.2) := by
    simpa only [A,Function.comp_def] using hV₀.comp_continuous hgraph hgraphMem
  have hBc : Continuous (fun p : K × ℝ => B p.1 p.2) := by
    simpa only [B,Function.comp_def] using hV₁.comp_continuous hgraph hgraphMem
  have hCc : Continuous (fun p : K × ℝ => C p.1 p.2) := by
    simpa only [C,Function.comp_def] using hV₂.comp_continuous hgraph hgraphMem
  have hDc : Continuous (fun p : K × ℝ => D p.1 p.2) := by
    simpa only [D,Function.comp_def] using hV₃.comp_continuous hgraph hgraphMem
  have hJ₂c : Continuous (fun p : K × ℝ => J₂ p.1 p.2) := hBc.clm_apply (𝕜 := ℝ) hAc
  have hJ₃c : Continuous (fun p : K × ℝ => J₃ p.1 p.2) :=
    ((hCc.clm_apply (𝕜 := ℝ) hAc).clm_apply (𝕜 := ℝ) hAc).add
      (hBc.clm_apply (𝕜 := ℝ) hJ₂c)
  have hFourthLeft :=
    ((((hDc.clm_apply (𝕜 := ℝ) hAc).clm_apply (𝕜 := ℝ) hAc).add
      (hCc.clm_apply (𝕜 := ℝ) hJ₂c)).clm_apply (𝕜 := ℝ) hAc).add
        ((hCc.clm_apply (𝕜 := ℝ) hAc).clm_apply (𝕜 := ℝ) hJ₂c)
  have hJ₄c : Continuous (fun p : K × ℝ => J₄ p.1 p.2) :=
    hFourthLeft.add (((hCc.clm_apply (𝕜 := ℝ) hAc).clm_apply (𝕜 := ℝ) hJ₂c).add
      (hBc.clm_apply (𝕜 := ℝ) hJ₃c))
  apply continuous_pi
  intro j
  fin_cases j
  · simpa only [iteratedDeriv_zero] using hy
  · change Continuous (fun p : K × ℝ => iteratedDeriv 1 (y p.1) p.2)
    simpa only [hjet₁] using hAc
  · change Continuous (fun p : K × ℝ => iteratedDeriv 2 (y p.1) p.2)
    simpa only [hjet₂] using hJ₂c
  · change Continuous (fun p : K × ℝ => iteratedDeriv 3 (y p.1) p.2)
    simpa only [hjet₃] using hJ₃c
  · change Continuous (fun p : K × ℝ => iteratedDeriv 4 (y p.1) p.2)
    simpa only [hjet₄] using hJ₄c

end Lemniscate
