import Lemniscate.NormalGraphPhaseVariation
import Lemniscate.NormalGraphRealLinePhase
import Lemniscate.NormalGraphPhaseChoice
import Lemniscate.PeriodicConjugation
import Lemniscate.PeriodicCurvatureProfileEntry

/-! An actual normal-projection family admits a C1 angle satisfying the
complex adjoint phase condition and tending to zero at the initial time. -/
noncomputable section
namespace Lemniscate
open Complex Set Filter
open scoped Topology ContDiff ComplexConjugate

/-- The geometric angular variation and the actual circle phase select
a small C1 angle. Only the L2 traces of the height and rotation field
are needed at the initial parameter; no initial time derivative or
geometric evolution equation is assumed. -/
theorem normal_graph_phase_fixed_family
    (L : ℝ) [Fact (0<L)]
    (T₀ a₀ : ℝ) (hT₀ : 0<T₀) (ha₀ : 0<a₀)
    (Y : ℝ → ℝ → ℂ) (β t n : ℝ → ℂ) (k : ℝ → ℝ)
    (χ H : (ℝ × ℝ) × ℝ → ℝ)
    (hY : ∀ r ∈ Ioo 0 T₀, ContDiff ℝ ∞ (Y r))
    (hYreg : ∀ r ∈ Ioo 0 T₀, ∀ s, deriv (Y r) s ≠ 0)
    (hχ : ContDiffOn ℝ ∞ χ
      ((Ioo 0 T₀ ×ˢ Ioo (-a₀) a₀) ×ˢ (univ : Set ℝ)))
    (hH : ContDiffOn ℝ ∞ H
      ((Ioo 0 T₀ ×ˢ Ioo (-a₀) a₀) ×ˢ (univ : Set ℝ)))
    (hχpos : ∀ q ∈ Ioo 0 T₀ ×ˢ Ioo (-a₀) a₀, ∀ s,
      0 < deriv (fun z => χ (q,z)) s)
    (hβ : ∀ s, HasDerivAt β (t s) s)
    (hn : ∀ s, HasDerivAt n (-(k s:ℂ)*t s) s)
    (hu : ∀ s, ‖t s‖=1) (hN : ∀ s, n s=I*t s)
    (hregular : ∀ q ∈ Ioo 0 T₀ ×ˢ Ioo (-a₀) a₀, ∀ s,
      0 < 1-k s*H (q,s))
    (hgraph : ∀ q ∈ Ioo 0 T₀ ×ˢ Ioo (-a₀) a₀, ∀ s,
      Y q.1 (χ (q,s)) = Complex.exp ((q.2:ℂ)*I)*
        normalGraphCurve β n (fun z => H (q,z)) s)
    (Q G : (ℝ × ℝ) → C(AddCircle L,ℂ)) (ψ : CircleL2 L)
    (hψ : circleConjugate L ψ=ψ)
    (hQ : ∀ q ∈ insert ((0:ℝ),0) (Ioo 0 T₀ ×ˢ Ioo (-a₀) a₀), ∀ s : ℝ,
      Q q (s:AddCircle L) = (H (q,s):ℂ))
    (hG : ∀ q ∈ Ioo 0 T₀ ×ˢ Ioo (-a₀) a₀, ∀ s : ℝ,
      G q (s:AddCircle L) =
        (((conj (t s)*β s).re+((conj (t s)*β s).im+H (q,s))*
          deriv (fun z => H (q,z)) s/(1-k s*H (q,s)):ℝ):ℂ))
    (hQtrace : ContinuousWithinAt (fun q => circleContinuousL2 L (Q q))
      (insert ((0:ℝ),0) (Ioo 0 T₀ ×ˢ Ioo (-a₀) a₀)) (0,0))
    (hGtrace : ContinuousWithinAt (fun q => circleContinuousL2 L (G q))
      (insert ((0:ℝ),0) (Ioo 0 T₀ ×ˢ Ioo (-a₀) a₀)) (0,0))
    (hphase₀ : inner ℂ ψ (circleContinuousL2 L (Q (0,0)))=0)
    (hpair₀ : (inner ℂ ψ (circleContinuousL2 L (G (0,0)))).re≠0) :
    ∃ T>0, T≤T₀ ∧ ∃ a>0, a≤a₀ ∧ ∃ θ : ℝ → ℝ,
      ContDiffOn ℝ 1 θ (Ioo 0 T) ∧
      Tendsto θ (𝓝[>] (0:ℝ)) (𝓝 0) ∧ θ 0=0 ∧
      ∀ r ∈ Ioo 0 T, |θ r|<a/2 ∧
        inner ℂ ψ (circleContinuousL2 L (Q (r,θ r)))=0 := by
  let U := Ioo (0:ℝ) T₀ ×ˢ Ioo (-a₀) a₀
  let K := insert ((0:ℝ),0) U
  let A := U ×ˢ (univ : Set ℝ)
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hA : IsOpen A := hU.prod isOpen_univ
  have hspace (F : (ℝ × ℝ) × ℝ → ℝ) (hF : ContDiffOn ℝ ∞ F A)
      (q : ℝ × ℝ) (hq : q ∈ U) : ContDiff ℝ ∞ (fun s => F (q,s)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro s
    have hdomain : A ∈ 𝓝 (q,s) := hA.mem_nhds ⟨hq,mem_univ s⟩
    exact (hF.contDiffAt hdomain).comp s (contDiffAt_const.prodMk contDiffAt_id)
  have hangular (F : (ℝ × ℝ) × ℝ → ℝ) (hF : ContDiffOn ℝ ∞ F A)
      (q : ℝ × ℝ) (hq : q ∈ U) (s : ℝ) :
      HasDerivAt (fun a => F ((q.1,a),s))
        (deriv (fun a => F ((q.1,a),s)) q.2) q.2 := by
    have hdomain : A ∈ 𝓝 (q,s) := hA.mem_nhds ⟨hq,mem_univ s⟩
    have hm : ContDiff ℝ ∞ (fun a : ℝ => ((q.1,a),s)) :=
      (contDiff_const.prodMk contDiff_id).prodMk contDiff_const
    exact (((hF.contDiffAt hdomain).comp q.2 hm.contDiffAt).differentiableAt
      (by simp)).hasDerivAt
  have hvariation (q : ℝ × ℝ) (hq : q ∈ U) (s : ℝ) :
      HasDerivAt (fun a => (H ((q.1,a),s):ℂ)) (-G q (s:AddCircle L)) q.2 := by
    have hm : Tendsto (fun a : ℝ => (q.1,a)) (𝓝 q.2) (𝓝 q) :=
      (continuous_const.prodMk continuous_id).continuousAt
    have hgerm : ∀ᶠ a in 𝓝 q.2, ∀ z,
        Y q.1 (χ ((q.1,a),z)) = Complex.exp ((a:ℂ)*I)*
          normalGraphCurve β n (fun z => H ((q.1,a),z)) z := by
      filter_upwards [hm.eventually (hU.mem_nhds hq)] with a ha
      exact hgraph (q.1,a) ha
    have hpoint := normal_graph_phase_variation (Y q.1) β t n k
      (fun a z => χ ((q.1,a),z)) (fun a z => H ((q.1,a),z)) q.2
      (fun z => deriv (fun a => χ ((q.1,a),z)) q.2)
      (fun z => deriv (fun a => H ((q.1,a),z)) q.2)
      (fun z => deriv (fun x => H (q,x)) z)
      (hY q.1 hq.1) (hYreg q.1 hq.1) (hspace χ hχ q hq)
      (hχpos q hq) (fun z => hangular χ hχ q hq z)
      (fun z => hangular H hH q hq z) hβ hn hu hN
      (fun z => ((hspace H hH q hq).differentiable (by simp) z).hasDerivAt)
      (hregular q hq) hgerm
    apply ((hangular H hH q hq s).ofReal_comp).congr_deriv
    simp only [hpoint s,hG q hq s,Complex.ofReal_neg]
  have horder : (1:ℕ∞ω) ≤ (∞:ℕ∞ω) :=
    (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 1)).le
  obtain ⟨hΦ,hΦd⟩ := normal_graph_real_line_phase L U hU H (hH.of_le horder)
    Q G ψ (fun q hq => hQ q (Or.inr hq)) hvariation
  let Φ : ℝ × ℝ → ℝ := fun q => (inner ℂ ψ (circleContinuousL2 L (Q q))).re
  let D : ℝ × ℝ → ℝ := fun q => -(inner ℂ ψ (circleContinuousL2 L (G q))).re
  have hEll : Continuous (fun v : CircleL2 L => (inner ℂ ψ v).re) := by
    simpa only [Function.comp_def,innerSL_apply_apply,Complex.reCLM_apply] using
      Complex.reCLM.continuous.comp (innerSL ℂ ψ).continuous
  have hΦtrace : ContinuousWithinAt Φ K (0,0) :=
    hEll.continuousAt.comp_continuousWithinAt hQtrace
  have hDtrace : ContinuousWithinAt D K (0,0) :=
    (hEll.continuousAt.comp_continuousWithinAt hGtrace).neg
  have hD₀ : D (0,0)≠0 := neg_ne_zero.mpr hpair₀
  have hangleD (r : ℝ) (hr : r ∈ Ioo 0 T₀) (a : ℝ) (ha : a ∈ Ioo (-a₀) a₀) :
      deriv (fun b => Φ (r,b)) a=D (r,a) := by
    simpa only [Φ,D,Complex.neg_re] using (hΦd r a ⟨hr,ha⟩).deriv
  have hId : Tendsto (fun r : ℝ => r) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hmap : Tendsto (fun r : ℝ => (r,(0:ℝ))) (𝓝[>] (0:ℝ)) (𝓝 ((0:ℝ),0)) :=
    Filter.Tendsto.prodMk_nhds hId tendsto_const_nhds
  have hmapK : Tendsto (fun r : ℝ => (r,(0:ℝ))) (𝓝[>] (0:ℝ)) (𝓝[K] (0,0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hmap,?_⟩
    filter_upwards [Ioo_mem_nhdsGT hT₀] with r hr
    exact Or.inr ⟨hr,⟨by linarith only [ha₀],ha₀⟩⟩
  have htrace : Tendsto (fun r => Φ (r,0)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hΦt : Tendsto Φ (𝓝[K] (0,0)) (𝓝 (Φ (0,0))) := hΦtrace
    have hh : Tendsto (fun r : ℝ => Φ (r,0)) (𝓝[>] (0:ℝ)) (𝓝 (Φ (0,0))) :=
      Filter.Tendsto.comp (f := fun r : ℝ => (r,(0:ℝ))) (g := Φ)
        (x := 𝓝[>] (0:ℝ)) (y := 𝓝[K] (0,0)) (z := 𝓝 (Φ (0,0))) hΦt hmapK
    simpa only [Φ,hphase₀,Complex.zero_re] using hh
  obtain ⟨T,hT,hTT₀,a,ha,haa₀,θ,hθ,hθtrace,hroot⟩ :=
    normal_graph_phase_choice Φ D T₀ a₀ hT₀ ha₀ hΦ hDtrace hD₀ hangleD htrace
  let θbar : ℝ → ℝ := fun r => if r=0 then 0 else θ r
  have hbar (r : ℝ) (hr : r ∈ Ioo 0 T) : θbar r=θ r := by
    simp only [θbar,if_neg (ne_of_gt hr.1)]
  have hbarC : ContDiffOn ℝ 1 θbar (Ioo 0 T) := hθ.congr hbar
  have hbarEq : θbar =ᶠ[𝓝[>] (0:ℝ)] θ := by
    have hpos : ∀ᶠ r : ℝ in 𝓝[>] (0:ℝ), 0<r := self_mem_nhdsWithin
    filter_upwards [hpos] with r hr
    simp only [θbar,if_neg (ne_of_gt hr)]
  have hbarTrace : Tendsto θbar (𝓝[>] (0:ℝ)) (𝓝 0) :=
    (tendsto_congr' hbarEq).mpr hθtrace
  have hbarZero : θbar 0=0 := by simp only [θbar,if_pos rfl]
  refine ⟨T,hT,hTT₀,a,ha,haa₀,θbar,hbarC,hbarTrace,hbarZero,?_⟩
  intro r hr
  rw [hbar r hr]
  refine ⟨(hroot r hr).1,?_⟩
  have hq : (r,θ r) ∈ U := by
    refine ⟨⟨hr.1,hr.2.trans_le hTT₀⟩,?_⟩
    apply abs_lt.mp
    exact (hroot r hr).1.trans_le (by linarith only [ha,haa₀])
  have hQreal : circleConjugate L (circleContinuousL2 L (Q (r,θ r))) =
      circleContinuousL2 L (Q (r,θ r)) := by
    apply circle_conjugate_continuous_real L (Q (r,θ r))
    intro x
    induction x using QuotientAddGroup.induction_on
    rename_i s
    simp only [hQ (r,θ r) (Or.inr hq) s,Complex.conj_ofReal]
  have him := circle_inner_im_eq_zero_of_real L ψ
    (circleContinuousL2 L (Q (r,θ r))) hψ hQreal
  apply Complex.ext
  · simpa only [Φ,Complex.zero_re] using (hroot r hr).2
  · simpa only [Complex.zero_im] using him

end Lemniscate
