import Migration.UniversalShortCore
import Migration.InitialDirectionalWidth

noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion

private theorem recessionThreshold_continuous : Continuous recessionThreshold := by
  unfold recessionThreshold
  apply (continuous_id.pow 3).div
    ((continuous_const.add (Real.continuous_sqrt.comp (continuous_const.mul continuous_id))).pow 2)
  exact fun x => pow_ne_zero _ (ne_of_gt (add_pos_of_pos_of_nonneg Real.pi_pos (Real.sqrt_nonneg _)))

variable (c : SmoothPeriodicImmersion (Ioi 0))

/-- Forward initial data are admitted with only joint one-sided continuity
of position and one-sided continuity of physical bending. The free elastic
equation is only used for strictly positive times. -/
theorem forward_common_disk_of_energy_drop (hf : c.IsNormalFEF)
    (hposition : ContinuousOn (fun z : ℝ × ℝ => c.position z.1 z.2) (Ici 0 ×ˢ univ))
    (henergy : ContinuousWithinAt c.bending (Ici 0) 0) :
    ∃ p : ℂ, ∀ {t η : ℝ}, 0 ≤ t → 0 < η → η < 2/3 →
      t*c.bending 0^3*(c.bending 0-c.bending t) < recessionThreshold η →
      Metric.closedBall p ((2/3-η)/c.bending 0) ⊆ convexHull ℝ (c.position t '' Icc 0 c.period) := by
  let E := c.bending 0
  let A := c.position 0 '' Icc 0 c.period
  have hc : Continuous (fun z : ℝ × ℝ => c.position (max z.1 0) z.2) :=
    hposition.comp_continuous ((continuous_fst.max continuous_const).prodMk continuous_snd)
      (fun z => ⟨show 0≤max z.1 0 from le_max_right _ _,mem_univ _⟩)
  have hc₀ : Continuous (c.position 0) := by
    simpa [Function.comp_def] using hc.comp ((continuous_const :
      Continuous (fun _ : ℝ => (0:ℝ))).prodMk continuous_id)
  have hE : 0<E := by
    have h := c.forward_initial_bending_mul_verticalWidth hposition henergy
    by_contra! hh
    rw [show c.bending 0=0 from le_antisymm hh (c.bending_nonneg 0),zero_mul] at h
    norm_num at h
  have hA : IsCompact A := isCompact_Icc.image hc₀
  have hw (e : ℂ) (he : ‖e‖=1) : ∃ x∈A, ∃ y∈A, 2/E ≤ inner ℝ e x-inner ℝ e y := by
    obtain ⟨lo,hi,hr,hb⟩ := c.forward_initial_directional_width hposition henergy e he
    obtain ⟨u,hu,hu'⟩ := hr.2.1
    obtain ⟨v,hv,hv'⟩ := hr.2.2
    refine ⟨c.position 0 v,⟨v,hv,rfl⟩,c.position 0 u,⟨u,hu,rfl⟩,?_⟩
    change 2/E ≤ innerSL ℝ e (c.position 0 v) - innerSL ℝ e (c.position 0 u)
    rw [hv',hu']
    exact (div_le_iff₀ hE).mpr (by linarith)
  obtain ⟨p,hp⟩ := exists_center_of_uniform_width hA (div_pos (by norm_num) hE) hw
  refine ⟨p,?_⟩
  intro t η ht hη hηmax htime x hx
  apply mem_convexHull_of_surrounding_directions
  intro e he
  let H : ℂ →L[ℝ] ℝ := innerSL ℝ e
  have hH : ‖H‖ ≤ 1 := by dsimp [H]; rw [innerSL_apply_norm,he]
  obtain ⟨_,⟨u,hu,rfl⟩,hsup⟩ := hp e he
  change H p + (2/E)/3 ≤ H (c.position 0 u) at hsup
  have hx' : H x - H p ≤ (2/3-η)/E := by
    have h := real_inner_le_norm e (x-p)
    rw [inner_sub_right,he,one_mul] at h
    exact h.trans (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)
  have hsqueeze : H x ≤ H (c.position 0 u)-η/E := by
    linarith [show (2/3-η)/E+η/E = (2/E)/3 by ring]
  rcases ht.eq_or_lt with hzero|htpos
  · refine ⟨c.position t u,⟨u,hu,rfl⟩,?_⟩
    change H x < H (c.position t u)
    rw [← hzero]
    linarith [div_pos hη hE]
  let P := t*E^3*(E-c.bending t)
  have htime₀ : P < recessionThreshold η := htime
  have hnear : ∀ᶠ z in 𝓝[<] η, P < recessionThreshold z :=
    (recessionThreshold_continuous.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).eventually (lt_mem_nhds htime₀)
  have hpos : ∀ᶠ z in 𝓝[<] η, 0<z := (lt_mem_nhds hη).filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ z in 𝓝[<] η, z<η := self_mem_nhdsWithin
  obtain ⟨δ,hδpos,hδη,hδtime⟩ := (hpos.and (hlt.and hnear)).exists
  have hδε : δ<η := hδη
  have hgap : H x < H (c.position 0 u)-δ/E := by
    linarith [div_lt_div_of_pos_right hδε hE]
  have hlimE : Tendsto c.bending (𝓝[>] 0) (𝓝 E) :=
    (henergy.mono (show Ioi (0:ℝ) ⊆ Ici 0 from fun _ h => le_of_lt (show (0:ℝ)<_ from h))).tendsto
  have hlimx : Tendsto (fun v : ℝ => v) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hlimP : Tendsto (fun v => (t-v)*c.bending v^3*(c.bending v-c.bending t))
      (𝓝[>] 0) (𝓝 P) := by
    simpa [P] using (((tendsto_const_nhds (x := t)).sub hlimx).mul (hlimE.pow 3)).mul
      (hlimE.sub (tendsto_const_nhds (x := c.bending t)))
  have hlimH : Tendsto (fun v => H (c.position v u)) (𝓝[>] 0) (𝓝 (H (c.position 0 u))) := by
    have k : Continuous (fun v : ℝ => H (c.position (max v 0) u)) :=
      H.continuous.comp (hc.comp (continuous_id.prodMk continuous_const))
    have k' : ContinuousOn (fun v => H (c.position v u)) (Ici 0) :=
      k.continuousOn.congr (fun v hv => by simp [max_eq_left (show 0≤v from hv)])
    exact ((k' 0 (by simp)).mono (show Ioi (0:ℝ) ⊆ Ici 0 from fun _ h => le_of_lt
      (show (0:ℝ)<_ from h))).tendsto
  have hevent_gap := (hlimH.sub ((tendsto_const_nhds (x := δ)).div hlimE hE.ne')).eventually
    (lt_mem_nhds hgap)
  have hevent_cost := hlimP.eventually (gt_mem_nhds hδtime)
  have hevent_t := hlimx.eventually (gt_mem_nhds htpos)
  have hright : ∀ᶠ v in 𝓝[>] (0:ℝ), 0<v := self_mem_nhdsWithin
  obtain ⟨v,hv,hvt,hpg,htc⟩ :=
    (hright.and (hevent_t.and (hevent_gap.and hevent_cost))).exists
  have hvpos : 0<v := hv
  have hvT : v<t := hvt
  have hev := c.bending_pos_of_width hvpos
  obtain ⟨lo,hi,hr,hwidth⟩ := c.directional_width_range hvpos e he
  have hW : δ/c.bending v ≤ hi-lo := by
    apply (div_le_iff₀ hev).mpr
    linarith
  have hslab : Icc v t ⊆ Ioi 0 := fun _ hh => lt_of_lt_of_le hvpos hh.1
  by_contra! hn
  have hmiss (z : ℝ) (hz : z ∈ Icc 0 c.period) : H (c.position t z) ≤ hi-δ/c.bending v := by
    have hz' : H (c.position t z) ≤ H x := hn _ ⟨z,hz,rfl⟩
    have hvH : H (c.position v u) ≤ hi := (hr.1 u hu).2
    change H x < H (c.position v u)-δ/c.bending v at hpg
    linarith
  have hcost := c.scaled_support_recession_cost hf H hH hvT hδpos hW hslab hev hr hmiss
  exact (not_lt_of_ge hcost) htc

theorem forward_universal_short_time_disk (hf : c.IsNormalFEF)
    (hposition : ContinuousOn (fun z : ℝ × ℝ => c.position z.1 z.2) (Ici 0 ×ˢ univ))
    (henergy : ContinuousWithinAt c.bending (Ici 0) 0) :
    ∃ p : ℂ, ∀ {t : ℝ}, 0 ≤ t →
      t*c.bending 0^4 < (1/27)/(Real.pi+Real.sqrt (2/3))^2 →
      Metric.closedBall p (1/(3*c.bending 0)) ⊆ convexHull ℝ (c.position t '' Icc 0 c.period) := by
  obtain ⟨p,hp⟩ := c.forward_common_disk_of_energy_drop hf hposition henergy
  refine ⟨p,?_⟩
  intro t ht htime
  have hbound : t*c.bending 0^3*(c.bending 0-c.bending t) ≤ t*c.bending 0^4 := by
    have := mul_nonneg (mul_nonneg ht (pow_nonneg (c.bending_nonneg 0) 3)) (c.bending_nonneg t)
    nlinarith
  have htime' : t*c.bending 0^3*(c.bending 0-c.bending t) < recessionThreshold (1/3) := by
    apply hbound.trans_lt
    norm_num [recessionThreshold] at htime ⊢
    exact htime
  have h := hp ht (by norm_num : (0:ℝ)<1/3) (by norm_num) htime'
  convert h using 2
  ring

#print axioms forward_common_disk_of_energy_drop
#print axioms forward_universal_short_time_disk
end MigrationGeometry.Flow.SmoothPeriodicImmersion
