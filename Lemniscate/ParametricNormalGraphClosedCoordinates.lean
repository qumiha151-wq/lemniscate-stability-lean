import Lemniscate.ParametricNormalGraphProjection
import Lemniscate.ParametricNormalProjectionTrace
import Lemniscate.NormalProjectionVectorField
import Lemniscate.NormalGraphGeometry
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Normal projection extends to an initially aligned graph on a closed
parameter set. Its actual spatial ODE includes the boundary parameter;
no extension across that parameter and no higher norm smallness is used. -/
noncomputable section
namespace Lemniscate
open Complex Filter Set
open scoped Topology ContDiff ComplexConjugate

private theorem continuousOn_of_product_subtype
    {P E : Type*} [TopologicalSpace P] [TopologicalSpace E]
    (K : Set P) (f : P × ℝ → E)
    (hf : Continuous (fun z : K × ℝ => f (z.1.val,z.2))) :
    ContinuousOn f (K ×ˢ (univ : Set ℝ)) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have h₁ : Continuous (fun z : (K ×ˢ (univ : Set ℝ)) =>
      (⟨z.val.1,z.property.1⟩ : K)) :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have h₂ : Continuous (fun z : (K ×ˢ (univ : Set ℝ)) => z.val.2) :=
    continuous_snd.comp continuous_subtype_val
  exact hf.comp (h₁.prodMk h₂)

private theorem initial_normal_projection_velocity
    (γ V β T : ℝ → ℂ) (κ h : ℝ → ℝ)
    (hγ : ∀ s, HasDerivAt γ (V s) s)
    (hgraph : ∀ s, γ s=β s+I*(h s:ℂ)*T s)
    (hβ : ∀ s, HasDerivAt β (T s) s)
    (hTd : ∀ s, HasDerivAt T (I*(κ s:ℂ)*T s) s)
    (hunit : ∀ s, ‖T s‖=1)
    (hκ : ContDiff ℝ ∞ κ) (hh : ContDiff ℝ ∞ h) :
    ∀ s, conj (T s)*V s=((1-κ s*h s:ℝ):ℂ)+I*((deriv h s:ℝ):ℂ) := by
  let n : ℝ → ℂ := fun s => I*T s
  have hts (s : ℝ) : HasDerivAt T ((κ s:ℂ)*n s) s := by
    apply (hTd s).congr_deriv
    dsimp only [n]
    ring
  have hns (s : ℝ) : HasDerivAt n (-(κ s:ℂ)*T s) s := by
    apply ((hTd s).const_mul I).congr_deriv
    calc
      I*(I*(κ s:ℂ)*T s) = I^2*((κ s:ℂ)*T s) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  have hh₁ : ContDiff ℝ ∞ (deriv h) := (contDiff_infty_iff_deriv.mp hh).2
  have hg := normal_graph_geometry β T n κ (deriv κ) h (deriv h) (deriv (deriv h))
    hβ hts hns (fun s => (hκ.differentiable (by simp) s).hasDerivAt)
    (fun s => (hh.differentiable (by simp) s).hasDerivAt)
    (fun s => (hh₁.differentiable (by simp) s).hasDerivAt) hunit (fun _ => rfl)
  have heq (s : ℝ) : γ s=normalGraphCurve β n h s := by
    rw [hgraph]
    dsimp only [normalGraphCurve,n]
    ring
  intro s
  have hv : V s=((1-κ s*h s:ℝ):ℂ)*T s+((deriv h s:ℝ):ℂ)*n s :=
    (hγ s).unique ((hg s).1.congr_of_eventuallyEq (Eventually.of_forall heq))
  have hself : conj (T s)*T s=1 := by rw [Complex.conj_mul',hunit]; simp
  rw [hv]
  calc
    _ = (((1-κ s*h s:ℝ):ℂ)+I*((deriv h s:ℝ):ℂ))*(conj (T s)*T s) := by
      dsimp only [n]
      ring
    _ = _ := by rw [hself,mul_one]

set_option maxHeartbeats 800000 in
/-- On an open parameter set together with one initially aligned boundary
parameter, the selected normal coordinates have their actual continuous
trace, smooth spatial slices and their actual spatial ODE. -/
theorem parametric_normal_graph_closed_coordinates
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    (U : Set P) (hU : IsOpen U) (p₀ : P) (hp₀ : p₀ ∉ U)
    (Γ V : P × ℝ → ℂ) (β T : ℝ → ℂ) (κ h₀ : ℝ → ℝ)
    (L δ K v : ℝ)
    (hΓsmooth : ContDiffOn ℝ ∞ Γ ((insert p₀ U) ×ˢ (univ : Set ℝ)))
    (hβsmooth : ContDiff ℝ ∞ β) (hTsmooth : ContDiff ℝ ∞ T)
    (hκsmooth : ContDiff ℝ ∞ κ) (hh₀smooth : ContDiff ℝ ∞ h₀)
    (hΓ : ∀ p ∈ insert p₀ U, ∀ s : ℝ, HasDerivAt (fun x => Γ (p,x)) (V (p,s)) s)
    (hβ : ∀ s, HasDerivAt β (T s) s)
    (hTd : ∀ s, HasDerivAt T (I*(κ s:ℂ)*T s) s)
    (hunit : ∀ s, ‖T s‖=1)
    (hspeed : ∀ p ∈ insert p₀ U, ∀ s : ℝ, ‖V (p,s)‖≤v)
    (hΓper : ∀ p ∈ insert p₀ U, Function.Periodic (fun s => Γ (p,s)) L)
    (hβper : Function.Periodic β L) (hh₀per : Function.Periodic h₀ L)
    (hinitial : ∀ s, Γ (p₀,s)=β s+I*(h₀ s:ℂ)*T s)
    (hδ : 0<δ) (hK : 0≤K) (hsmall : δ+2*K*δ<1/2)
    (hregular : K*(δ+2*v*δ)<1)
    (hposition : ∀ p ∈ insert p₀ U, ∀ s : ℝ, ‖Γ (p,s)-β s‖≤δ)
    (htangent : ∀ p ∈ insert p₀ U, ∀ s : ℝ, ‖V (p,s)-T s‖≤δ)
    (hcurvature : ∀ s, |κ s|≤K) :
    ∃ χ H : P × ℝ → ℝ,
      (∀ s, χ (p₀,s)=s ∧ H (p₀,s)=h₀ s) ∧
      ContinuousOn χ ((insert p₀ U) ×ˢ (univ : Set ℝ)) ∧
      ContinuousOn H ((insert p₀ U) ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞ χ (U ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞ H (U ×ˢ (univ : Set ℝ)) ∧
      ∀ p ∈ insert p₀ U,
        ContDiff ℝ ∞ (fun s => χ (p,s)) ∧ ContDiff ℝ ∞ (fun s => H (p,s)) ∧
        (∀ s, χ (p,s+L)=χ (p,s)+L) ∧ Function.Periodic (fun s => H (p,s)) L ∧
        ∀ s : ℝ,
          Γ (p,χ (p,s))=β s+I*(H (p,s):ℂ)*T s ∧ |χ (p,s)-s|<3*δ ∧
          0<1-κ s*H (p,s) ∧ 0<deriv (fun x => χ (p,x)) s ∧
          HasDerivAt (fun x => (x,(χ (p,x)-x,H (p,x))))
            (normalProjectionVectorField T κ V (p,(s,(χ (p,s)-s,H (p,s))))) s := by
  classical
  let C : Set P := insert p₀ U
  have hpBase : p₀ ∈ C := mem_insert p₀ U
  have hUsub : U ⊆ C := subset_insert p₀ U
  have hΓU := hΓsmooth.mono (prod_mono_left hUsub)
  obtain ⟨χu,Hu,hχu,hHu,hdata⟩ := parametric_normal_graph_projection U hU Γ V β T κ L δ K v
    hΓU hβsmooth (fun p hp => hΓ p (hUsub hp)) hβ hTd
    (fun p hp => hspeed p (hUsub hp)) hunit (fun p hp => hΓper p (hUsub hp)) hβper
    hδ hK hsmall hregular (fun p hp => hposition p (hUsub hp))
    (fun p hp => htangent p (hUsub hp)) hcurvature
  let χ : P × ℝ → ℝ := fun z => if z.1=p₀ then z.2 else χu z
  let H : P × ℝ → ℝ := fun z => if z.1=p₀ then h₀ z.2 else Hu z
  have hχ0 (s : ℝ) : χ (p₀,s)=s := if_pos rfl
  have hH0 (s : ℝ) : H (p₀,s)=h₀ s := if_pos rfl
  have hne (p : P) (hp : p ∈ U) : p≠p₀ := fun heq => hp₀ (heq ▸ hp)
  have hχeq (p : P) (hp : p ∈ U) (s : ℝ) : χ (p,s)=χu (p,s) := if_neg (hne p hp)
  have hHeq (p : P) (hp : p ∈ U) (s : ℝ) : H (p,s)=Hu (p,s) := if_neg (hne p hp)
  have hχsmooth : ContDiffOn ℝ ∞ χ (U ×ˢ (univ : Set ℝ)) :=
    hχu.congr (fun z hz => hχeq z.1 hz.1 z.2)
  have hHsmooth : ContDiffOn ℝ ∞ H (U ×ˢ (univ : Set ℝ)) :=
    hHu.congr (fun z hz => hHeq z.1 hz.1 z.2)
  have hW0 := initial_normal_projection_velocity (fun s => Γ (p₀,s)) (fun s => V (p₀,s))
    β T κ h₀ (hΓ p₀ hpBase) hinitial hβ hTd hunit hκsmooth hh₀smooth
  have hH0small (s : ℝ) : |h₀ s|≤δ := by
    have hh := hposition p₀ hpBase s
    rw [hinitial,add_sub_cancel_left] at hh
    simpa only [norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,hunit,
      mul_one,one_mul] using hh
  have hA0 (s : ℝ) : 0<1-κ s*h₀ s := by
    have hb : |κ s*h₀ s|≤K*δ := by
      rw [abs_mul]
      exact mul_le_mul (hcurvature s) (hH0small s) (abs_nonneg _) hK
    have hs : K*δ<1 := by linarith only [hsmall,hδ]
    have ha := (le_abs_self (κ s*h₀ s)).trans_lt (hb.trans_lt hs)
    linarith only [ha]
  have hpoint (p : P) (hp : p ∈ C) (s : ℝ) :
      Γ (p,χ (p,s))=β s+I*(H (p,s):ℂ)*T s ∧
      |χ (p,s)-s|≤2*|(conj (T s)*(Γ (p,s)-β s)).re| ∧
      |χ (p,s)-s|<3*δ ∧ 0<1-κ s*H (p,s) ∧
      HasDerivAt (fun x => χ (p,x))
        ((1-κ s*H (p,s))/(conj (T s)*V (p,χ (p,s))).re) s ∧
      0<deriv (fun x => χ (p,x)) s ∧
      HasDerivAt (fun x => H (p,x))
        (deriv (fun x => χ (p,x)) s*(conj (T s)*V (p,χ (p,s))).im) s := by
    by_cases hpp : p=p₀
    · subst p
      have hχfn : (fun x => χ (p₀,x))=id := funext hχ0
      have hHfn : (fun x => H (p₀,x))=h₀ := funext hH0
      have hχd : HasDerivAt (fun x => χ (p₀,x)) 1 s := by simpa only [hχfn] using hasDerivAt_id s
      have hHd : HasDerivAt (fun x => H (p₀,x)) (deriv h₀ s) s := by
        simpa only [hHfn] using (hh₀smooth.differentiable (by simp) s).hasDerivAt
      have hRe : (conj (T s)*V (p₀,s)).re=1-κ s*h₀ s := by
        rw [hW0 s]
        simp [Complex.mul_re]
      have hIm : (conj (T s)*V (p₀,s)).im=deriv h₀ s := by
        rw [hW0 s]
        simp [Complex.mul_im]
      refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
      · simpa only [hχ0,hH0] using hinitial s
      · rw [hχ0,sub_self,abs_zero]
        exact mul_nonneg (by norm_num) (abs_nonneg _)
      · rw [hχ0,sub_self,abs_zero]
        positivity
      · simpa only [hH0] using hA0 s
      · apply hχd.congr_deriv
        rw [hH0,hχ0,hRe,div_self (hA0 s).ne']
      · rw [hχd.deriv]
        norm_num
      · apply hHd.congr_deriv
        rw [hχd.deriv,hχ0,hIm,one_mul]
    · have hpU : p ∈ U := (mem_insert_iff.mp hp).resolve_left hpp
      have hd := (hdata p hpU).2.2 s
      have hχfn : (fun x => χ (p,x))=(fun x => χu (p,x)) := funext (hχeq p hpU)
      have hHfn : (fun x => H (p,x))=(fun x => Hu (p,x)) := funext (hHeq p hpU)
      have hres : |χ (p,s)-s|≤2*|(conj (T s)*(Γ (p,s)-β s)).re| := by
        simpa only [hχeq p hpU] using hd.2.1
      have hr : |χ (p,s)-s|<3*δ := by
        have hb : |(conj (T s)*(Γ (p,s)-β s)).re|≤δ := by
          calc
            _ ≤ ‖conj (T s)*(Γ (p,s)-β s)‖ := Complex.abs_re_le_norm _
            _ = ‖Γ (p,s)-β s‖ := by rw [norm_mul,Complex.norm_conj,hunit,one_mul]
            _ ≤ δ := hposition p hp s
        linarith only [hres,hb,hδ]
      refine ⟨?_,hres,hr,?_,?_,?_,?_⟩
      · simpa only [hχeq p hpU,hHeq p hpU] using hd.1
      · simpa only [hHeq p hpU] using hd.2.2.2.1
      · simpa only [hχfn,hχeq p hpU,hHeq p hpU] using hd.2.2.2.2.1
      · simpa only [hχfn] using hd.2.2.2.2.2.1
      · simpa only [hχfn,hHfn,hχeq p hpU] using hd.2.2.2.2.2.2
  let pBase : C := ⟨p₀,hpBase⟩
  let incl : C × ℝ → P × ℝ := fun z => (z.1.val,z.2)
  have hIncl : Continuous incl :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hΓC : Continuous (fun z : C × ℝ => Γ (z.1.val,z.2)) :=
    hΓsmooth.continuousOn.comp_continuous hIncl (fun z => ⟨z.1.property,mem_univ _⟩)
  have hχoff (z : C × ℝ) (hz : z.1≠pBase) :
      ContinuousAt (fun z : C × ℝ => χ (z.1.val,z.2)) z := by
    have hne0 : z.1.val≠p₀ := fun heq => hz (Subtype.ext heq)
    have hpU : z.1.val ∈ U := (mem_insert_iff.mp z.1.property).resolve_left hne0
    have hat : ContinuousAt χ (z.1.val,z.2) :=
      (hχsmooth.continuousOn (z.1.val,z.2) ⟨hpU,mem_univ _⟩).continuousAt
        ((hU.prod isOpen_univ).mem_nhds ⟨hpU,mem_univ _⟩)
    have hi : ContinuousAt incl z := hIncl.continuousAt
    have hc := ContinuousAt.comp (f := incl) (g := χ) (x := z) hat hi
    simpa only [incl,Function.comp_def] using! hc
  have htrace := parametric_normal_projection_trace_continuous pBase
    (fun z : C × ℝ => Γ (z.1.val,z.2)) hΓC β T hβsmooth.continuous hTsmooth.continuous hunit
    h₀ hinitial (fun z : C × ℝ => χ (z.1.val,z.2)) (fun z : C × ℝ => H (z.1.val,z.2))
    hχ0 hχoff (fun p _ s => (hpoint p.val p.property s).2.1)
    (fun p s => (hpoint p.val p.property s).1)
  have hχC := continuousOn_of_product_subtype C χ htrace.1
  have hHC := continuousOn_of_product_subtype C H htrace.2
  refine ⟨χ,H,fun s => ⟨hχ0 s,hH0 s⟩,hχC,hHC,hχsmooth,hHsmooth,?_⟩
  intro p hp
  have hslices : ContDiff ℝ ∞ (fun s => χ (p,s)) ∧ ContDiff ℝ ∞ (fun s => H (p,s)) := by
    by_cases hpp : p=p₀
    · subst p
      exact ⟨by simpa only [χ,if_pos rfl,id_eq] using! (contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ)),
        by simpa only [H,if_pos rfl] using hh₀smooth⟩
    · have hpU : p ∈ U := (mem_insert_iff.mp hp).resolve_left hpp
      constructor
      · apply contDiff_iff_contDiffAt.mpr
        intro s
        exact (hχsmooth.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hpU,mem_univ s⟩)).comp s
          (contDiffAt_const.prodMk contDiffAt_id)
      · apply contDiff_iff_contDiffAt.mpr
        intro s
        exact (hHsmooth.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hpU,mem_univ s⟩)).comp s
          (contDiffAt_const.prodMk contDiffAt_id)
  have hperiod : (∀ s, χ (p,s+L)=χ (p,s)+L) ∧ Function.Periodic (fun s => H (p,s)) L := by
    by_cases hpp : p=p₀
    · subst p
      exact ⟨fun s => by rw [hχ0,hχ0],fun s => by simpa only [hH0] using hh₀per s⟩
    · have hpU : p ∈ U := (mem_insert_iff.mp hp).resolve_left hpp
      constructor
      · intro s
        have hh := (hdata p hpU).1 s
        simp only [hχeq p hpU] at ⊢
        linarith only [hh]
      · intro s
        simpa only [hHeq p hpU] using (hdata p hpU).2.1 s
  refine ⟨hslices.1,hslices.2,hperiod.1,hperiod.2,?_⟩
  intro s
  have hd := hpoint p hp s
  have hχd := hd.2.2.2.2.1
  have hHd := hd.2.2.2.2.2.2
  have hState : HasDerivAt (fun x : ℝ => (x,(χ (p,x)-x,H (p,x))))
      (1,(((1-κ s*H (p,s))/(conj (T s)*V (p,χ (p,s))).re)-1,
        deriv (fun x => χ (p,x)) s*(conj (T s)*V (p,χ (p,s))).im)) s := by
    simpa only [id_eq,Pi.sub_apply] using!
      HasDerivAt.prodMk (hasDerivAt_id s)
        (HasDerivAt.prodMk (hχd.sub (hasDerivAt_id s)) hHd)
  refine ⟨hd.1,hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2.2.1,?_⟩
  apply hState.congr_deriv
  rw [hχd.deriv]
  dsimp only [normalProjectionVectorField]
  rw [show s+(χ (p,s)-s)=χ (p,s) by ring]

end Lemniscate
