import Migration.CurveKinematics
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace MigrationGeometry.Flow.SmoothPeriodicImmersion

variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

private theorem normalized_label {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    ∃ v ∈ Icc 0 c.period, c.position t v = c.position t u := by
  refine ⟨toIcoMod c.period_pos 0 u,
    Ico_subset_Icc_self (toIcoMod_mem_Ico' c.period_pos u), ?_⟩
  rw [← self_sub_toIcoDiv_zsmul c.period_pos 0 u]
  exact (c.periodic t ht).sub_zsmul_eq _

private theorem nearby_vertical_labels {t u l : ℝ} (ht : t ∈ I)
    (hh : (c.position t u).im < l)
    (hx : deriv (fun v => (c.position t v).re) u ≠ 0) :
    ∀ᶠ s in 𝓝 t, ∃ v, (c.position s v).re = (c.position t u).re ∧
      (c.position s v).im < l := by
  let z : ℝ × ℝ := (t,u)
  let x := fun p : ℝ × ℝ => (c.position p.1 p.2).re
  let f := fun p : ℝ × ℝ => (p.1, x p)
  let D := fderiv ℝ x z
  have hI := (c.time_open.prod isOpen_univ).mem_nhds (show z ∈ I ×ˢ (univ : Set ℝ) from ⟨ht,trivial⟩)
  have hc := (c.joint_smooth.contDiffAt hI)
  have hx' : ContDiffAt ℝ ∞ x z := Complex.reCLM.contDiff.contDiffAt.comp z hc
  have hd := hx'.hasStrictFDerivAt (by simp)
  have h1 : D (0,1) ≠ 0 := by
    have hv := (hd.hasFDerivAt.comp_hasDerivAt u
      ((hasDerivAt_const u t).prodMk (hasDerivAt_id u))).deriv
    exact hv ▸ hx
  have hdf : HasStrictFDerivAt f ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod D) z :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasStrictFDerivAt.prodMk hd
  have hsurj : Function.Surjective ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod D) := by
    rintro ⟨a,b⟩
    let v := (b-D (a,0))/D (0,1)
    refine ⟨(a,v),Prod.ext rfl ?_⟩
    change D (a,v) = b
    rw [show (a,v)=(a,0)+v • ((0,1) : ℝ × ℝ) by simp, map_add, map_smul]
    dsimp [v]
    field_simp
    ring
  have hmap := hdf.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hsurj)
  let S : Set (ℝ × ℝ) := {p | (c.position p.1 p.2).im < l}
  have hS : S ∈ 𝓝 z := (Complex.continuous_im.continuousAt.comp hc.continuousAt).eventually_lt
    (continuousAt_const (y := l)) hh
  have hImage : f '' S ∈ 𝓝 (t,x z) := hmap ▸ Filter.image_mem_map hS
  have hn := (continuous_id.prodMk (continuous_const (y := x z))).continuousAt hImage
  filter_upwards [hn] with s hs
  obtain ⟨⟨t',v⟩,hv,he⟩ := hs
  have ht' : t'=s := congrArg Prod.fst he
  subst t'
  exact ⟨v,congrArg Prod.snd he,hv⟩

/-- If the entire portion below a level is transverse to a vertical line up
to a given time, every point of the cap's horizontal projection at that
time has already been attained at the level itself. -/
theorem vertical_line_hits_gap_level {s T l x₀ : ℝ} (hsT : s ≤ T)
    (hslab : Icc s T ⊆ I) (hinit : ∀ u, l < (c.position s u).im)
    (htrans : ∀ t ∈ Icc s T, ∀ u, (c.position t u).re = x₀ →
      (c.position t u).im < l → deriv (fun v => (c.position t v).re) u ≠ 0)
    (hcap : ∃ u, (c.position T u).re = x₀ ∧ (c.position T u).im ≤ l) :
    ∃ t ∈ Ioc s T, ∃ u, (c.position t u).re = x₀ ∧ (c.position t u).im = l := by
  let D : Set (ℝ × ℝ) := Icc s T ×ˢ Icc 0 c.period
  let f := fun p : ℝ × ℝ => (p.1, c.position p.1 p.2)
  let V : Set (ℝ × ℂ) := {q | q.2.re = x₀ ∧ q.2.im ≤ l}
  have hD : IsCompact D := isCompact_Icc.prod isCompact_Icc
  have hf : ContinuousOn f D := continuous_fst.continuousOn.prodMk
    (c.joint_smooth.continuousOn.mono (fun _ h => ⟨hslab h.1,trivial⟩))
  have hV : IsClosed V := (isClosed_eq (Complex.continuous_re.comp continuous_snd) continuous_const).inter
    (isClosed_le (Complex.continuous_im.comp continuous_snd) continuous_const)
  have hC := (hD.image_of_continuousOn hf).inter_right hV
  have hin {t u : ℝ} (ht : t ∈ Icc s T) (hx : (c.position t u).re=x₀)
      (hh : (c.position t u).im≤l) : (t,c.position t u) ∈ f '' D ∩ V := by
    obtain ⟨v,hv,he⟩ := c.normalized_label (hslab ht) u
    exact ⟨⟨(t,v),⟨ht,hv⟩,Prod.ext rfl he⟩,hx,hh⟩
  obtain ⟨uT,hxT,hhT⟩ := hcap
  obtain ⟨_,⟨⟨⟨t,u⟩,htD,rfl⟩,hv⟩,hm⟩ := hC.exists_isMinOn
    ⟨_,hin ⟨hsT,le_rfl⟩ hxT hhT⟩ continuous_fst.continuousOn
  have ht := htD.1
  have hx : (c.position t u).re=x₀ := hv.1
  have hh : (c.position t u).im≤l := hv.2
  have hst : s<t := lt_of_le_of_ne ht.1 (by rintro rfl; exact (hinit u).not_ge hh)
  refine ⟨t,⟨hst,ht.2⟩,u,hx,hh.eq_of_not_lt ?_⟩
  intro hlt
  have hn := c.nearby_vertical_labels (hslab ht) hlt (htrans t ht u hx hlt)
  obtain ⟨t',htt,hst',v,hx',hh'⟩ := ((lt_mem_nhds hst).and hn).exists_lt
  exact htt.not_ge (hm (hin ⟨hst'.le,htt.le.trans ht.2⟩ (hx'.trans hx) hh'.le))

/-- Height is the first coordinate so ordinary product disintegration takes
horizontal sections. All material labels are included. -/
def sweptBandTrace (s T : ℝ) : Set (ℝ × ℝ) :=
  {q | ∃ t ∈ Icc s T, ∃ u, q = ((c.position t u).im,(c.position t u).re)}

theorem sweptBandTrace_compact {s T : ℝ} (hslab : Icc s T ⊆ I) :
    IsCompact (c.sweptBandTrace s T) := by
  let f := fun p : ℝ × ℝ => ((c.position p.1 p.2).im,(c.position p.1 p.2).re)
  let D := Icc s T ×ˢ Icc 0 c.period
  have hc := c.joint_smooth.continuousOn.mono (show D ⊆ I ×ˢ (univ : Set ℝ) from
    fun _ h => ⟨hslab h.1,trivial⟩)
  have hf : ContinuousOn f D :=
    (Complex.continuous_im.comp_continuousOn hc).prodMk (Complex.continuous_re.comp_continuousOn hc)
  have he : f '' D = c.sweptBandTrace s T := by
    ext q
    constructor
    · rintro ⟨⟨t,v⟩,ht,rfl⟩
      exact ⟨t,ht.1,v,rfl⟩
    · rintro ⟨t,ht,u,rfl⟩
      obtain ⟨v,hv,he⟩ := c.normalized_label (hslab ht) u
      exact ⟨(t,v),⟨ht,hv⟩,by simp [f,he]⟩
  rw [← he]
  exact (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn hf

theorem cap_projection_in_section {s T τ l u₁ u₂ : ℝ} (hτ : τ ∈ Icc s T)
    (hslab : Icc s T ⊆ I) (hinit : ∀ u, l < (c.position s u).im)
    (htrans : ∀ t ∈ Icc s τ, ∀ u, (c.position t u).im < l →
      deriv (fun v => (c.position t v).re) u ≠ 0)
    (hcap : ∀ u ∈ uIcc u₁ u₂, (c.position τ u).im ≤ l) :
    uIcc (c.position τ u₁).re (c.position τ u₂).re ⊆
      Prod.mk l ⁻¹' c.sweptBandTrace s T := by
  intro x hx
  have hc := Complex.continuous_re.comp (c.position_slice_smooth (hslab hτ)).continuous
  obtain ⟨u,hu,he⟩ := intermediate_value_uIcc hc.continuousOn hx
  obtain ⟨t,ht,v,hx',hl'⟩ := c.vertical_line_hits_gap_level hτ.1
    (fun _ ht => hslab ⟨ht.1,ht.2.trans hτ.2⟩) hinit
    (fun t ht w _ => htrans t ht w) ⟨u,he,hcap _ hu⟩
  exact ⟨t,⟨ht.1.le,ht.2.trans hτ.2⟩,v,Prod.ext hl'.symm hx'.symm⟩

/-- An area estimate for the physical image. Cap times and material arcs
may vary with the height, with no measurable choice assumption. -/
theorem gap_area_of_caps {s T a b W : ℝ} (hslab : Icc s T ⊆ I)
    (hinit : ∀ u, a ≤ (c.position s u).im)
    (hcaps : ∀ l ∈ Ioo b a, ∃ τ ∈ Icc s T, ∃ u₁ u₂ : ℝ,
      (∀ t ∈ Icc s τ, ∀ u, (c.position t u).im < l →
        deriv (fun v => (c.position t v).re) u ≠ 0) ∧
      (∀ u ∈ uIcc u₁ u₂, (c.position τ u).im ≤ l) ∧
      W ≤ |(c.position τ u₂).re - (c.position τ u₁).re|) :
    ENNReal.ofReal W * ENNReal.ofReal (a-b) ≤
      (volume.prod volume) ((Ioo b a ×ˢ univ) ∩ c.sweptBandTrace s T) := by
  have hmeas : MeasurableSet ((Ioo b a ×ˢ univ) ∩ c.sweptBandTrace s T) :=
    (measurableSet_Ioo.prod MeasurableSet.univ).inter
    (c.sweptBandTrace_compact hslab).measurableSet
  rw [Measure.prod_apply hmeas, ← Real.volume_Ioo, ← lintegral_indicator_const measurableSet_Ioo]
  apply lintegral_mono
  intro l
  by_cases hl : l ∈ Ioo b a
  · rw [indicator_of_mem hl]
    obtain ⟨τ,hτ,u₁,u₂,htrans,hcap,hwidth⟩ := hcaps l hl
    have hsub := c.cap_projection_in_section hτ hslab (fun u => hl.2.trans_le (hinit u)) htrans hcap
    calc
      ENNReal.ofReal W ≤ volume (uIcc (c.position τ u₁).re (c.position τ u₂).re) := by
        rw [uIcc,Real.volume_Icc, sup_sub_inf_eq_abs_sub]
        exact ENNReal.ofReal_le_ofReal hwidth
      _ ≤ volume (Prod.mk l ⁻¹' ((Ioo b a ×ˢ univ) ∩ c.sweptBandTrace s T)) :=
        measure_mono (fun x hx => ⟨⟨hl,trivial⟩,hsub hx⟩)
  · simp [hl]

end MigrationGeometry.Flow.SmoothPeriodicImmersion
