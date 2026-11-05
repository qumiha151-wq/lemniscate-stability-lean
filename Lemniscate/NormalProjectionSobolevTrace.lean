import Lemniscate.NormalGraphProjectionSpatialJet
import Lemniscate.PeriodicContinuousSpatialJetFamily
import Lemniscate.ParameterDerivativeEstimate

/-! The actual normal-projection height has a continuous H4 trace on
the parameter domain, including its initial boundary. -/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped ContDiff Topology

private theorem trace_clm_iterated_deriv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (g : ℝ → E) (hg : ContDiff ℝ ∞ g)
    (j : Fin 5) (s : ℝ) :
    L (iteratedDeriv j.val g s) = iteratedDeriv j.val (fun x => L (g x)) s := by
  have hshift : ContDiffAt ℝ (4:ℕ) (fun a : ℝ => g (a+s)) 0 :=
    ((hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)).comp
      (contDiff_id.add contDiff_const)).contDiffAt
  have h := continuous_linear_map_iterated_deriv L (fun a : ℝ => g (a+s))
    4 j.val hshift (Nat.le_of_lt_succ j.isLt)
  let G : ℝ → F := fun x => L (g x)
  change L (iteratedDeriv j.val (fun a : ℝ => g (a+s)) 0) =
    iteratedDeriv j.val (fun a : ℝ => G (a+s)) 0 at h
  simpa only [iteratedDeriv_comp_add_const,zero_add] using! h

/-- Uniform velocity proximity and the actual normal-projection spatial
ODE give a continuous H4 family of heights up to a parameter boundary.
Individual spatial smoothness is used only to commute the fixed height
projection with actual iterated derivatives; no parameter derivative or
joint higher-jet continuity of the height is assumed. -/
theorem normal_projection_sobolev_trace
    (ℓ : ℝ) [Fact (0 < ℓ)]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (U : Set P) (hU : UniqueDiffOn ℝ U) (V : P × ℝ → ℂ)
    (hV : ContDiffOn ℝ ∞ V (U ×ˢ (univ : Set ℝ)))
    (T : ℝ → ℂ) (κ : ℝ → ℝ)
    (hT : ContDiff ℝ ∞ T) (hκ : ContDiff ℝ ∞ κ)
    (hTd : ∀ s, HasDerivAt T (I*(κ s:ℂ)*T s) s)
    (hunit : ∀ s, ‖T s‖=1)
    (δ K r : ℝ) (hK : 0≤K) (hsmall : δ+K*r<1)
    (hcurvature : ∀ s, |κ s|≤K)
    (hclose : ∀ p ∈ U, ∀ x : ℝ, ‖V (p,x)-T x‖≤δ)
    (y : U → ℝ → NormalProjectionState)
    (hy : Continuous (fun z : U × ℝ => y z.1 z.2))
    (hslicey : ∀ p : U, ContDiff ℝ ∞ (y p))
    (hdisplacement : ∀ p s, |(y p s).2.1|<r)
    (hODE : ∀ p s, HasDerivAt (y p)
      (normalProjectionVectorField T κ V ((p:P),y p s)) s)
    (H : P × ℝ → ℂ)
    (hheight : ∀ p (hp : p ∈ U) s, H (p,s) = ((y ⟨p,hp⟩ s).2.2:ℂ))
    (hperiodic : ∀ p ∈ U, Function.Periodic (fun s => H (p,s)) ℓ) :
    ∃ F : Fin 5 → P → C(AddCircle ℓ,ℂ),
      (∀ j, ContinuousOn (F j) U) ∧
      (∀ p ∈ U, ∀ (j : Fin 5) (s : ℝ),
        F j p (s:AddCircle ℓ) = iteratedDeriv j.val (fun x => H (p,x)) s) ∧
      ∃ u : P → CircleSobolevSpace ℓ 4, ContinuousOn u U ∧
        ∀ p ∈ U, ∀ j : Fin 5,
          circleSobolevCoordinate ℓ 4 j (u p) = circleContinuousL2 ℓ (F j p) := by
  let L : NormalProjectionState →L[ℝ] ℂ := Complex.ofRealCLM.comp
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
  have hH (p : U) : (fun s => H ((p:P),s)) = fun s => L (y p s) :=
    funext fun s => hheight p.val p.property s
  have hsmooth (p : P) (hp : p ∈ U) : ContDiff ℝ ∞ (fun s => H (p,s)) := by
    rw [hH ⟨p,hp⟩]
    exact L.contDiff.comp (hslicey ⟨p,hp⟩)
  have hjet (p : U) (j : Fin 5) (s : ℝ) :
      iteratedDeriv j.val (fun x => H ((p:P),x)) s =
        L (iteratedDeriv j.val (y p) s) := by
    rw [hH p]
    exact (trace_clm_iterated_deriv L (y p) (hslicey p) j s).symm
  have hstate := normal_graph_projection_spatial_jet U hU V hV T κ hT hκ hTd hunit
    δ K r hK hsmall hcurvature hclose y hy hdisplacement hODE
  let D := U ×ˢ (univ : Set ℝ)
  let inc : D → U × ℝ := fun z => (⟨z.val.1,z.property.1⟩,z.val.2)
  have hinc : Continuous inc :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk
      (fun z : D => z.property.1)).prodMk (continuous_snd.comp continuous_subtype_val)
  have hjoint (j : Fin 5) :
      ContinuousOn (fun z : P × ℝ => iteratedDeriv j.val (fun x => H (z.1,x)) z.2) D := by
    have hsj : Continuous (fun z : U × ℝ => iteratedDeriv j.val (y z.1) z.2) :=
      (continuous_apply j).comp hstate
    have hHj : Continuous (fun z : U × ℝ =>
        iteratedDeriv j.val (fun x => H ((z.1:P),x)) z.2) := by
      simpa only [Function.comp_def,hjet] using! L.continuous.comp hsj
    apply continuousOn_iff_continuous_domRestrict.mpr
    simpa only [inc,Function.comp_def] using! hHj.comp hinc
  exact periodic_continuous_spatial_jet_family ℓ 4 U H hsmooth hperiodic hjoint

end Lemniscate
