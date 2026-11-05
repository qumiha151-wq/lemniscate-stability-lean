import Lemniscate.FreeElasticFlow
import Lemniscate.StaticCurveReparametrization
import Lemniscate.ArclengthOrbitCharacterization
import Mathlib.Topology.Instances.NNReal.Lemmas

/-! Return the constructed physical flow to the original initial
parametrization. Joint smoothness up to the initial boundary is
preserved by the fixed smooth oriented parameter change. -/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped ContDiff ComplexConjugate NNReal

/-- A constructed physical flow and its actual initial parameter change
give a jointly smooth flow in the original parametrization on the
closed nonnegative time axis. -/
theorem lemniscate_constructed_flow
    (Core : ℝ → ℝ → ℂ) (hCore : IsFreeElasticFlow Core)
    (ell : ℝ)
    (hsmooth : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => Core z.1 z.2)
      (Ici (0:ℝ) ×ˢ (univ : Set ℝ)))
    (hperiod : ∀ t : ℝ,0≤t → Function.Periodic (Core t) ell)
    (e₀ : ℝ ≃o ℝ) (he₀ : ContDiff ℝ ∞ (e₀ : ℝ → ℝ))
    (he₀i : ContDiff ℝ ∞ (e₀.symm : ℝ → ℝ))
    (hdeck : ∀ s : ℝ,e₀ (s+ell)=e₀ s+2*Real.pi)
    (γ₀ : ℝ → ℂ) (hinitial : ∀ s : ℝ,Core 0 s=γ₀ (e₀ s)) :
    ∃ Y : ℝ → ℝ → ℂ,
      (∀ t s,Y t s=Core t (e₀.symm s)) ∧
      IsFreeElasticFlow Y ∧ (∀ s : ℝ,Y 0 s=γ₀ s) ∧
      ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => Y z.1 z.2)
        (Ici (0:ℝ) ×ˢ (univ : Set ℝ)) ∧
      (∀ t : ℝ,0≤t → Function.Periodic (Y t) (2*Real.pi)) ∧
      ∀ t : ℝ,0≤t → OrientedCurveEquivalent (Y t) (Core t) (2*Real.pi) ell := by
  classical
  let Y : ℝ → ℝ → ℂ := fun t s => Core t (e₀.symm s)
  have hspace (t : ℝ) (ht : 0≤t) : ContDiff ℝ ∞ (Core t) := by
    apply contDiffOn_univ.mp
    exact hsmooth.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun s _ => ⟨ht,mem_univ s⟩)
  have hpositive (s : ℝ) : 0<deriv (e₀.symm : ℝ → ℝ) s :=
    order_iso_deriv_pos e₀.symm (he₀i.differentiable (by simp))
      (he₀.differentiable (by simp)) s
  have hflow : IsFreeElasticFlow Y := by
    intro t ht
    let V : ℝ → ℂ := fun s => Classical.choose (hCore t ht s)
    have hV (s : ℝ) :
        HasDerivWithinAt (fun z => Core z s) (V s) (Ici (0:ℝ)) t ∧
        deriv (Core t) s≠0 ∧
        (((conj (V s)*(I*deriv (Core t) s/(‖deriv (Core t) s‖:ℂ))).re:ℂ)*
          (I*deriv (Core t) s/(‖deriv (Core t) s‖:ℂ)))=
            -(planarElasticForce (Core t) s:ℂ)*
              (I*deriv (Core t) s/(‖deriv (Core t) s‖:ℂ)) :=
      Classical.choose_spec (hCore t ht s)
    have hpoint (s : ℝ) :
        let n := I*deriv (Core t) s/(‖deriv (Core t) s‖:ℂ)
        HasDerivWithinAt (fun z => Core z s) (V s) (Ici (0:ℝ)) t ∧
          deriv (Core t) s≠0 ∧ ‖n‖=1 ∧
          (((conj (V s)*n).re:ℂ)*n)=
            -((arclengthDerivative (Core t)
                (arclengthDerivative (Core t) (planarSignedCurvature (Core t))) s+
              (1/2:ℝ)*(planarSignedCurvature (Core t) s)^3:ℝ):ℂ)*n := by
      dsimp only
      refine ⟨(hV s).1,(hV s).2.1,?_,?_⟩
      · rw [norm_div,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,
          Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
        exact div_self (norm_ne_zero_iff.mpr (hV s).2.1)
      · simpa only [planarElasticForce] using (hV s).2.2
    have hstatic := static_reparametrization_free_elastic_flow Core
      (e₀.symm : ℝ → ℝ) (Ici (0:ℝ)) t V (hspace t ht) he₀i hpositive hpoint
    intro s
    refine ⟨V (e₀.symm s),(hstatic s).1,(hstatic s).2.1,?_⟩
    simpa only [Y,planarElasticForce] using! (hstatic s).2.2.2
  have hinverseDeck (s : ℝ) : e₀.symm (s+2*Real.pi)=e₀.symm s+ell := by
    apply e₀.injective
    rw [e₀.apply_symm_apply,hdeck,e₀.apply_symm_apply]
  have hper (t : ℝ) (ht : 0≤t) : Function.Periodic (Y t) (2*Real.pi) := by
    intro s
    change Core t (e₀.symm (s+2*Real.pi))=Core t (e₀.symm s)
    rw [hinverseDeck]
    exact hperiod t ht (e₀.symm s)
  have hmap : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (z.1,e₀.symm z.2)) :=
    contDiff_fst.prodMk (he₀i.comp contDiff_snd)
  have hY : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => Y z.1 z.2)
      (Ici (0:ℝ) ×ˢ (univ : Set ℝ)) :=
    hsmooth.comp hmap.contDiffOn (fun z hz => ⟨hz.1,mem_univ _⟩)
  refine ⟨Y,fun _ _ => rfl,hflow,?_,hY,hper,?_⟩
  · intro s
    dsimp only [Y]
    rw [hinitial,e₀.apply_symm_apply]
  · intro t ht
    exact ⟨e₀,he₀,he₀i,hdeck,fun s => by simp only [Y,e₀.symm_apply_apply]⟩

end Lemniscate
