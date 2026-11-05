import Lemniscate.FreeElasticFlow
import Lemniscate.StaticCurveReparametrization
import Lemniscate.ArclengthOrbitCharacterization
import Lemniscate.CurveFamilySimilarityContinuity
import Mathlib.Topology.Instances.NNReal.Lemmas

/-! Return the constructed physical flow to the original initial
parametrization. All geometric identities come from static oriented
reparametrization; no time regularity beyond the actual flow is imposed. -/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped ContDiff ComplexConjugate NNReal

/-- A constructed physical flow and its actual initial parameter change
give a flow in the original parametrization, with the closed-time C1
continuity required by geometric stability. -/
theorem lemniscate_constructed_flow
    (Core : ℝ → ℝ → ℂ) (hCore : IsFreeElasticFlow Core)
    (ell : ℝ)
    (hspace : ∀ t : ℝ,0≤t → ContDiff ℝ ∞ (Core t))
    (hperiod : ∀ t : ℝ,0≤t → Function.Periodic (Core t) ell)
    (hposition : ContinuousOn (fun z : ℝ × ℝ => Core z.1 z.2)
      (Ici (0:ℝ) ×ˢ (univ : Set ℝ)))
    (hvelocity : ContinuousOn (fun z : ℝ × ℝ => deriv (Core z.1) z.2)
      (Ici (0:ℝ) ×ˢ (univ : Set ℝ)))
    (e₀ : ℝ ≃o ℝ) (he₀ : ContDiff ℝ ∞ (e₀ : ℝ → ℝ))
    (he₀i : ContDiff ℝ ∞ (e₀.symm : ℝ → ℝ))
    (hdeck : ∀ s : ℝ,e₀ (s+ell)=e₀ s+2*Real.pi)
    (γ₀ : ℝ → ℂ) (hinitial : ∀ s : ℝ,Core 0 s=γ₀ (e₀ s)) :
    ∃ Y : ℝ → ℝ → ℂ,
      (∀ t s,Y t s=Core t (e₀.symm s)) ∧
      IsFreeElasticFlow Y ∧ (∀ s : ℝ,Y 0 s=γ₀ s) ∧
      (∀ t : ℝ,0≤t → ContDiff ℝ ∞ (Y t) ∧
        Function.Periodic (Y t) (2*Real.pi)) ∧
      ContinuousOn (fun z : ℝ × ℝ => Y z.1 z.2)
        (Ici (0:ℝ) ×ˢ (univ : Set ℝ)) ∧
      ContinuousOn (fun z : ℝ × ℝ => deriv (Y z.1) z.2)
        (Ici (0:ℝ) ×ˢ (univ : Set ℝ)) ∧
      ∀ t : ℝ,0≤t → OrientedCurveEquivalent (Y t) (Core t) (2*Real.pi) ell := by
  classical
  let Y : ℝ → ℝ → ℂ := fun t s => Core t (e₀.symm s)
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
  have hsp (t : ℝ) (ht : 0≤t) :
      ContDiff ℝ ∞ (Y t) ∧ Function.Periodic (Y t) (2*Real.pi) := by
    refine ⟨(hspace t ht).comp he₀i,?_⟩
    intro s
    change Core t (e₀.symm (s+2*Real.pi))=Core t (e₀.symm s)
    rw [hinverseDeck]
    exact hperiod t ht (e₀.symm s)
  let G : ℝ≥0 × ℝ → ℂ := fun z => Core (z.1:ℝ) z.2
  let embed : ℝ≥0 × ℝ → ℝ × ℝ := fun z => ((z.1:ℝ),z.2)
  have hembed : Continuous embed :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hmaps (z : ℝ≥0 × ℝ) : embed z∈Ici (0:ℝ) ×ˢ (univ : Set ℝ) :=
    ⟨z.1.property,mem_univ z.2⟩
  have hG : Continuous G := by
    simpa only [G,embed,Function.comp_def] using!
      hposition.comp_continuous hembed hmaps
  have hGv : Continuous (fun z : ℝ≥0 × ℝ => deriv (fun s => G (z.1,s)) z.2) := by
    simpa only [G,embed,Function.comp_def] using!
      hvelocity.comp_continuous hembed hmaps
  have hGd (σ : ℝ≥0) : Differentiable ℝ (fun s => G (σ,s)) :=
    (hspace (σ:ℝ) σ.property).differentiable (by simp)
  have horder : (1:ℕ∞ω)≤(∞:ℕ∞ω) :=
    (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 1)).le
  have hsimilarity := curve_family_similarity_continuity G hG hGv hGd
    (fun σ : ℝ≥0 => σ) continuous_id (fun _ => (0:ℂ)) (fun _ => (1:ℂ))
      continuous_const continuous_const (e₀.symm : ℝ → ℝ) (he₀i.of_le horder)
  let Yn : ℝ≥0 × ℝ → ℂ := fun z => Y (z.1:ℝ) z.2
  have hYn : Continuous Yn ∧
      Continuous (fun z : ℝ≥0 × ℝ => deriv (fun s => Yn (z.1,s)) z.2) := by
    simpa only [Yn,Y,G,zero_add,one_mul] using! hsimilarity
  let retract : ℝ × ℝ → ℝ≥0 × ℝ := fun z => (Real.toNNReal z.1,z.2)
  have hretract : Continuous retract :=
    (continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd
  have hYc : ContinuousOn (fun z : ℝ × ℝ => Y z.1 z.2)
      (Ici (0:ℝ) ×ˢ (univ : Set ℝ)) := by
    apply (hYn.1.comp hretract).continuousOn.congr
    intro z hz
    simp only [Function.comp_def,retract,Yn,Real.coe_toNNReal z.1 hz.1]
  have hYv : ContinuousOn (fun z : ℝ × ℝ => deriv (Y z.1) z.2)
      (Ici (0:ℝ) ×ˢ (univ : Set ℝ)) := by
    apply (hYn.2.comp hretract).continuousOn.congr
    intro z hz
    simp only [Function.comp_def,retract,Yn,Real.coe_toNNReal z.1 hz.1]
  refine ⟨Y,fun _ _ => rfl,hflow,?_,hsp,hYc,hYv,?_⟩
  · intro s
    dsimp only [Y]
    rw [hinitial,e₀.apply_symm_apply]
  · intro t ht
    exact ⟨e₀,he₀,he₀i,hdeck,fun s => by simp only [Y,e₀.symm_apply_apply]⟩

end Lemniscate
