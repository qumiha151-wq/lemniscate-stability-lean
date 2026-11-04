import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! A smooth parameter implicit equation on an explicit open set of real
Banach spaces. The common inverse neighborhood is chosen using first
derivatives only. Higher smoothness then holds at every point of the
same parameter ball, without asking for analyticity.

-/
noncomputable section
namespace Lemniscate
open Filter Set
open scoped Topology ContDiff

/-- An invertible derivative in the unknown produces a C-infinity branch
on one common open parameter ball, with uniform local uniqueness. -/
theorem banach_implicit_equation
    {P E G : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (F : P × E → G) (d : P × E →L[ℝ] G) (e : E ≃L[ℝ] G)
    (S : Set (P × E)) (hS : IsOpen S) (h0 : ((0:P),(0:E)) ∈ S)
    (hF : ContDiffOn ℝ ∞ F S) (hFzero : F ((0:P),(0:E)) = 0)
    (hd : HasFDerivAt F d ((0:P),(0:E)))
    (he : ∀ u : E, d ((0:P),u) = e u) :
    ∃ ε > 0, ∃ r > 0, ∃ g : P → E,
      g 0 = 0 ∧ ContDiffOn ℝ ∞ g (Metric.ball 0 ε) ∧
      ∀ p : P, ‖p‖ < ε →
        ‖g p‖ < r ∧ F (p,g p) = 0 ∧
          ∀ u : E, ‖u‖ < r → F (p,u) = 0 → u = g p := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hF0 : ContDiffAt ℝ ∞ F ((0:P),(0:E)) := hF.contDiffAt (hS.mem_nhds h0)
  have hpartial : (fderiv ℝ F ((0:P),(0:E))).comp
      (ContinuousLinearMap.inr ℝ P E) = e.toContinuousLinearMap := by
    rw [hd.fderiv]
    ext u
    exact he u
  have hi : ((fderiv ℝ F ((0:P),(0:E))).comp
      (ContinuousLinearMap.inr ℝ P E)).IsInvertible := ⟨e,hpartial.symm⟩
  let data := (hF0.hasStrictFDerivAt hn).implicitFunctionDataOfProdDomain hi
  let H : P × E → G × P := data.prodFun
  let I := data.toOpenPartialHomeomorph
  have hHdef : H = (fun x : P × E => (F x,x.1)) := rfl
  have hIdef : (I : P × E → G × P) = H := data.toOpenPartialHomeomorph_coe
  have hH : ContDiffOn ℝ ∞ H S := by
    simpa only [hHdef] using hF.prodMk contDiff_fst.contDiffOn
  have hH0 : ContDiffAt ℝ ∞ H ((0:P),(0:E)) := hH.contDiffAt (hS.mem_nhds h0)
  obtain ⟨A0,hA0⟩ := data.isInvertible_fderiv_prodFun
  change (A0 : P × E →L[ℝ] G × P) = fderiv ℝ H ((0:P),(0:E)) at hA0
  have hIsoNhds :
      range (fun A : (P × E) ≃L[ℝ] (G × P) => (A : P × E →L[ℝ] G × P)) ∈
        𝓝 (fderiv ℝ H ((0:P),(0:E))) := by
    rw [← hA0]
    exact A0.nhds
  have hIsoEvent := (hH0.continuousAt_fderiv hn).preimage_mem_nhds hIsoNhds
  have hgood : ∀ᶠ x : P × E in 𝓝 ((0:P),(0:E)), x ∈ S ∧
      ∃ A : (P × E) ≃L[ℝ] (G × P), (A : P × E →L[ℝ] G × P) = fderiv ℝ H x := by
    filter_upwards [hS.mem_nhds h0,hIsoEvent] with x hx hA
    exact ⟨hx,hA⟩
  have hsource0 : ((0:P),(0:E)) ∈ I.source := data.pt_mem_toOpenPartialHomeomorph_source
  have hIzero : I ((0:P),(0:E)) = ((0:G),(0:P)) := by
    simpa only [hHdef,hFzero] using
      congrArg (fun f : P × E → G × P => f ((0:P),(0:E))) hIdef
  have htarget0 : ((0:G),(0:P)) ∈ I.target := by
    simpa only [hIzero] using I.map_source hsource0
  have hback0 : I.symm ((0:G),(0:P)) = ((0:P),(0:E)) := by
    simpa only [hIzero] using I.left_inv hsource0
  let g : P → E := fun p => (I.symm ((0:G),p)).2
  have hgzero : g 0 = 0 := congrArg Prod.snd hback0
  have hq : Continuous (fun p : P => ((0:G),p)) := continuous_const.prodMk continuous_id
  have hqSmooth : ContDiff ℝ ∞ (fun p : P => ((0:G),p)) :=
    contDiff_const.prodMk contDiff_id
  have hJcont : ContinuousAt (fun p : P => I.symm ((0:G),p)) (0:P) :=
    (I.continuousAt_symm htarget0).comp hq.continuousAt
  have hJtend : Tendsto (fun p : P => I.symm ((0:G),p)) (𝓝 0) (𝓝 ((0:P),(0:E))) := by
    simpa only [hback0] using hJcont.tendsto
  have hgcont : ContinuousAt g (0:P) := hJcont.snd
  obtain ⟨r,hr,hsourceBall⟩ := Metric.mem_nhds_iff.mp (I.open_source.mem_nhds hsource0)
  have hgBall : ∀ᶠ p : P in 𝓝 0, ‖g p‖ < r := by
    have hball : Metric.ball (0:E) r ∈ 𝓝 (g 0) := by
      rw [hgzero]
      exact Metric.ball_mem_nhds 0 hr
    filter_upwards [hgcont.tendsto.eventually hball] with p hp
    simpa only [Metric.mem_ball,dist_zero_right] using hp
  have htargetEvent : ∀ᶠ p : P in 𝓝 0, ((0:G),p) ∈ I.target :=
    hq.continuousAt.preimage_mem_nhds (I.open_target.mem_nhds htarget0)
  have hparams := htargetEvent.and ((hJtend.eventually hgood).and hgBall)
  obtain ⟨δ,hδ,hparamBall⟩ := Metric.eventually_nhds_iff.mp hparams
  let ε : ℝ := min r δ
  have hε : 0 < ε := lt_min hr hδ
  have hdata (p : P) (hp : ‖p‖ < ε) :=
    hparamBall (show dist p (0:P) < δ from by
      simpa only [dist_zero_right] using hp.trans_le (min_le_right r δ))
  refine ⟨ε,hε,r,hr,g,hgzero,?_,?_⟩
  · intro p hp
    have hp' : ‖p‖ < ε := by simpa only [Metric.mem_ball,dist_zero_right] using hp
    have hdat := hdata p hp'
    obtain ⟨A,hA⟩ := hdat.2.1.2
    have hcH : ContDiffAt ℝ ∞ H (I.symm ((0:G),p)) :=
      hH.contDiffAt (hS.mem_nhds hdat.2.1.1)
    have hcI : ContDiffAt ℝ ∞ I (I.symm ((0:G),p)) := by
      simpa only [hIdef] using hcH
    have hdI : HasFDerivAt I (A : P × E →L[ℝ] G × P) (I.symm ((0:G),p)) := by
      simpa only [hIdef,hA] using (hcH.hasStrictFDerivAt hn).hasFDerivAt
    have hinv : ContDiffAt ℝ ∞ I.symm ((0:G),p) :=
      I.contDiffAt_symm hdat.1 hdI hcI
    have hgp : ContDiffAt ℝ ∞ g p :=
      contDiffAt_snd.comp p (hinv.comp p hqSmooth.contDiffAt)
    exact hgp.contDiffWithinAt
  · intro p hp
    have hdat := hdata p hp
    have hright := I.right_inv hdat.1
    have hx : (I.symm ((0:G),p)).1 = p := by
      simpa only [hIdef,hHdef] using congrArg Prod.snd hright
    have hFx : F (I.symm ((0:G),p)) = 0 := by
      simpa only [hIdef,hHdef] using congrArg Prod.fst hright
    have hsolve : F (p,g p) = 0 := by
      change F (p,(I.symm ((0:G),p)).2) = 0
      have hpoint : (p,(I.symm ((0:G),p)).2) = I.symm ((0:G),p) :=
        Prod.ext hx.symm rfl
      exact (congrArg F hpoint).trans hFx
    refine ⟨hdat.2.2,hsolve,?_⟩
    intro u hu hFu
    have hpr : ‖p‖ < r := hp.trans_le (min_le_left r δ)
    have hpu : (p,u) ∈ Metric.ball ((0:P),(0:E)) r := by
      simpa only [Metric.mem_ball,Prod.dist_eq,dist_zero_right] using max_lt hpr hu
    have hinverse := I.left_inv (hsourceBall hpu)
    have hb : I.symm ((0:G),p) = (p,u) := by
      simpa only [hIdef,hHdef,hFu] using hinverse
    exact (congrArg Prod.snd hb).symm

end Lemniscate
