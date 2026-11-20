import LengthGrowth.ActualFlow.CubicMomentDissipation
import LengthGrowth.ActualFlow.RecordSelection
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Data.EReal.Basic
import Mathlib.Order.LiminfLimsup

/-! A half-threshold for signed cubic curvature on actual unbounded product
records. The underlying residual is a centered material square. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion

variable (c : ForwardImmersion)

def rootBending (t : ℝ) : ℝ := Real.sqrt (2*c.normalizedProduct t)

def signedCubicRatio (t : ℝ) : ℝ :=
  c.length t * materialCubicCurvature (c.position t) c.period /
    (2*c.energy t*c.rootBending t)

private theorem rootBending_pos {t : ℝ} (ht : 0≤t) : 0<c.rootBending t := by
  apply Real.sqrt_pos_of_pos
  unfold normalizedProduct
  have := c.energy_pos ht
  have := c.length_pos ht
  positivity

theorem rootBending_sq {t : ℝ} (_ht : 0≤t) :
    c.rootBending t^2=2*c.normalizedProduct t := by
  apply Real.sq_sqrt
  have h := c.normalizedProduct_nonneg t
  linarith

/-- Completing the material force square and subtracting its spatial mean. -/
theorem centered_cubic_deficit {t : ℝ} (ht : 0≤t) :
    let L := c.length t
    let B := 2*c.energy t
    let C := materialCubicCurvature (c.position t) c.period
    let S := materialSignedCurvature (c.position 0) c.period
    (2*L*C-B*S)^2 ≤ 16*L^2*(L*c.dissipation t-c.energy t*c.lengthRate t)+L*B^3 := by
  let γ := c.position t
  let L := c.length t
  let B := 2*c.energy t
  let C := materialCubicCurvature γ c.period
  let S := materialSignedCurvature γ c.period
  let Z := (2*L*C-B*S)/L
  have hs := c.position_slice_smooth ht
  have hr := c.immersion t ht
  have hl : 0<L := c.length_pos ht
  have hid := integral_weighted_affine_square
    (curvature_smooth hs hr).continuous (force_smooth hs hr).continuous
    (speed_smooth hs hr).continuous c.period (4*L) B Z
  have hn : 0 ≤ ∫ u in 0..c.period, (4*L*force γ u-B*curvature γ u-Z)^2*speed γ u :=
    intervalIntegral.integral_nonneg_of_forall c.period_pos.le
      (fun u => mul_nonneg (sq_nonneg _) (speed_pos hr u).le)
  have he : (∫ u in 0..c.period, curvature γ u^2*speed γ u)=B := by
    change (∫ u in 0..c.period, curvature γ u^2*speed γ u) =
      2*((1/2:ℝ)*(∫ u in 0..c.period, curvature γ u^2*speed γ u))
    ring
  change (∫ u in 0..c.period, (4*L*force γ u-B*curvature γ u-Z)^2*speed γ u) =
    (4*L)^2*c.dissipation t+B^2*_+Z^2*L+(-2*(4*L)*B)*c.lengthRate t+
    (-2*(4*L)*Z)*(∫ u in 0..c.period, force γ u*speed γ u)+(2*B*Z)*S at hid
  rw [hid,he,integral_force_eq_half_cubic hs hr (c.periodic t ht)] at hn
  change 0≤(4*L)^2*c.dissipation t+B^2*B+Z^2*L+(-2*(4*L)*B)*c.lengthRate t+
    (-2*(4*L)*Z)*((1/2)*C)+(2*B*Z)*S at hn
  dsimp only
  rw [← c.signedCurvature_eq_initial ht]
  change (2*L*C-B*S)^2≤16*L^2*(L*c.dissipation t-c.energy t*c.lengthRate t)+L*B^3
  have halg : L*((4*L)^2*c.dissipation t+B^2*B+Z^2*L+(-2*(4*L)*B)*c.lengthRate t+
      (-2*(4*L)*Z)*((1/2)*C)+(2*B*Z)*S)=
      16*L^2*(L*c.dissipation t-c.energy t*c.lengthRate t)+L*B^3-(2*L*C-B*S)^2 := by
    dsimp only [Z,B]
    field_simp [hl.ne']
    ring
  linarith only [halg,mul_nonneg hl.le hn]

/-- In the unit-length clock dτ = L⁻⁴dt, the left factor L⁴ times the
physical negative product derivative is exactly -d(EL)/dτ. -/
theorem normalized_cubic_deficit_bound {t : ℝ} (ht : 0≤t) :
    (2*c.normalizedProduct t)^3 *
      ((2*c.signedCubicRatio t-materialSignedCurvature (c.position 0) c.period/c.rootBending t)^2-1)/16 ≤
    c.length t^4*(c.length t*c.dissipation t-c.energy t*c.lengthRate t) := by
  let L := c.length t
  let A := 2*c.energy t
  let C := materialCubicCurvature (c.position t) c.period
  let S := materialSignedCurvature (c.position 0) c.period
  let R := c.rootBending t
  have hL : 0<L := c.length_pos ht
  have hA : 0<A := by dsimp [A]; have := c.energy_pos ht; positivity
  have hR : 0<R := c.rootBending_pos ht
  have hb : 2*c.normalizedProduct t=A*L := by unfold normalizedProduct; dsimp [A,L]; ring
  have hr : R^2=A*L := (c.rootBending_sq ht).trans hb
  have hid : (A*L)^3*((2*(L*C/(A*R))-S/R)^2-1) =
      L^2*((2*L*C-A*S)^2-L*A^3) := by
    field_simp [hA.ne',hR.ne']
    rw [hr]
    ring
  change (2*c.normalizedProduct t)^3*((2*(L*C/(A*R))-S/R)^2-1)/16 ≤ _
  rw [hb,hid]
  have h := c.centered_cubic_deficit ht
  change (2*L*C-A*S)^2≤16*L^2*(L*c.dissipation t-c.energy t*c.lengthRate t)+L*A^3 at h
  change _≤L^4*(L*c.dissipation t-c.energy t*c.lengthRate t)
  nlinarith only [mul_le_mul_of_nonneg_left h (sq_nonneg L)]

private theorem product_rate_nonneg_at_record (hf : c.IsNormalFEF) {t : ℝ} (ht : 0<t)
    (hr : ∀ x ∈ Icc 0 t, c.normalizedProduct x ≤ c.normalizedProduct t) :
    0≤c.energy t*c.lengthRate t-c.length t*c.dissipation t := by
  have hs := (hasDerivAt_iff_tendsto_slope_left_right.mp (c.normalizedProduct_hasDerivAt_normal hf ht)).1
  apply ge_of_tendsto hs
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds ht)] with x hx hx0
  rw [slope_def_field]
  exact div_nonneg_of_nonpos (sub_nonpos.mpr (hr x ⟨hx0.le,hx.le⟩)) (sub_nonpos.mpr hx.le)

theorem signedCubicRatio_record (hf : c.IsNormalFEF) {t : ℝ} (ht : 0<t)
    (hr : ∀ x ∈ Icc 0 t, c.normalizedProduct x ≤ c.normalizedProduct t) :
    2*c.rootBending t*|c.signedCubicRatio t| ≤
      c.rootBending t+|materialSignedCurvature (c.position 0) c.period| := by
  let L := c.length t
  let B := 2*c.energy t
  let C := materialCubicCurvature (c.position t) c.period
  let S := materialSignedCurvature (c.position 0) c.period
  let R := c.rootBending t
  have hB : 0<B := by dsimp [B]; have := c.energy_pos ht.le; positivity
  have hR : 0<R := c.rootBending_pos ht.le
  have hRs : R^2=B*L := by
    have eq := c.rootBending_sq ht.le
    simpa [R,B,L,normalizedProduct,mul_assoc] using eq
  have h := c.centered_cubic_deficit ht.le
  have hd := c.product_rate_nonneg_at_record hf ht hr
  change (2*L*C-B*S)^2 ≤ 16*L^2*(L*c.dissipation t-c.energy t*c.lengthRate t)+L*B^3 at h
  change 0≤c.energy t*c.lengthRate t-L*c.dissipation t at hd
  have h' : (2*L*C-B*S)^2 ≤ (B*R)^2 := by
    rw [mul_pow,hRs]
    nlinarith only [h,mul_nonneg (sq_nonneg L) hd]
  have hg := abs_le_of_sq_le_sq h' (mul_pos hB hR).le
  have htri := abs_add_le (2*L*C-B*S) (B*S)
  rw [sub_add_cancel,abs_mul B S,abs_of_pos hB,show 2*L*C=2*(L*C) by ring,
    abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at htri
  change 2*R*|(L*C)/(B*R)|≤R+|S|
  rw [abs_div, abs_of_pos (mul_pos hB hR),
    show 2*R*(|L*C|/(B*R))=2*|L*C|/B by field_simp [hB.ne',hR.ne']]
  apply (div_le_iff₀ hB).mpr
  rw [mul_assoc (2:ℝ) L C] at hg
  linarith only [hg,htri]

theorem product_at_supercritical_record (hf : c.IsNormalFEF) {t g : ℝ}
    (ht : 0<t) (hg : 1/2<g) (hm : g≤|c.signedCubicRatio t|)
    (hr : ∀ x ∈ Icc 0 t, c.normalizedProduct x ≤ c.normalizedProduct t) :
    c.normalizedProduct t ≤
      (|materialSignedCurvature (c.position 0) c.period|/(2*g-1))^2/2 := by
  have hw := c.signedCubicRatio_record hf ht hr
  have hroot := c.rootBending_pos ht.le
  have hw' : c.rootBending t ≤ |materialSignedCurvature (c.position 0) c.period|/(2*g-1) := by
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith only [hw,mul_le_mul_of_nonneg_left hm hroot.le]
  have hsq := pow_le_pow_left₀ hroot.le hw' 2
  rw [c.rootBending_sq ht.le] at hsq
  linarith

/-- All future products are bounded by the larger of the prefix maximum
and the explicit supercritical record threshold. -/
theorem supercritical_product_barrier (hf : c.IsNormalFEF) {T g M : ℝ}
    (hT : 0≤T) (hg : 1/2<g)
    (hprefix : ∀ x ∈ Icc 0 T, c.normalizedProduct x≤M)
    (hm : ∀ t>T, g≤|c.signedCubicRatio t|) {t : ℝ} (ht : 0≤t) :
    c.normalizedProduct t ≤ max M
      ((|materialSignedCurvature (c.position 0) c.period|/(2*g-1))^2/2) := by
  obtain ⟨s,hs,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr ht)
    (c.normalizedProduct_continuousOn.mono (fun _ hx => hx.1))
  apply (hmax (show t∈Icc 0 t from ⟨ht,le_rfl⟩)).trans
  by_cases hsT : s≤T
  · exact (hprefix s ⟨hs.1,hsT⟩).trans (le_max_left _ _)
  · have hsT' := lt_of_not_ge hsT
    apply (c.product_at_supercritical_record hf (hT.trans_lt hsT') hg (hm s hsT') _).trans (le_max_right _ _)
    exact fun x hx => hmax ⟨hx.1,hx.2.trans hs.2⟩

theorem quarter_bounds_of_eventual_supercritical_cubic (hf : c.IsNormalFEF)
    {g : ℝ} (hg : 1/2<g) (hm : ∀ᶠ t : ℝ in atTop, g≤|c.signedCubicRatio t|) :
    c.HasQuarterLengthBound ∧ c.HasQuarterEnergyBound := by
  obtain ⟨T,hT⟩ := eventually_atTop.1 hm
  let T' := max 0 T
  have hpos : 0≤T' := le_max_left _ _
  obtain ⟨x,_,hx⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hpos)
    (c.normalizedProduct_continuousOn.mono (fun _ h => h.1))
  have hb : c.HasBoundedEnergyLength := by
    refine ⟨_,fun t ht => c.supercritical_product_barrier hf hpos hg
      (fun _ h => hx h) (fun s hs => hT s ((le_max_right 0 T).trans hs.le)) ht⟩
  have hl := (c.quarter_length_iff_bounded_energyLength hf).mpr hb
  exact ⟨hl,c.quarter_energy_of_quarter_length hf hl⟩

/-- Extended-real liminf includes the case where the absolute signed ratio
escapes to infinity. -/
theorem quarter_bounds_of_liminf_cubic_gt_half (hf : c.IsNormalFEF)
    (hm : ((1/2:ℝ):EReal) < liminf (fun t : ℝ => ((|c.signedCubicRatio t|:ℝ):EReal)) atTop) :
    c.HasQuarterLengthBound ∧ c.HasQuarterEnergyBound := by
  obtain ⟨g,hg,hl⟩ := EReal.exists_between_coe_real hm
  apply c.quarter_bounds_of_eventual_supercritical_cubic hf (EReal.coe_lt_coe_iff.mp hg)
  exact (eventually_lt_of_lt_liminf hl).mono (fun t h => (EReal.coe_lt_coe_iff.mp h).le)

/-- For every requested starting time and high product there is a later
actual record. The signed cubic ratio is at most one half plus the given
explicit turning correction at that very record. -/
theorem high_record_cubic_half_of_failure (hf : c.IsNormalFEF)
    (hnot : ¬ c.HasQuarterLengthBound) (K T : ℝ) :
    ∃ t, T<t ∧ 0<t ∧ K<c.normalizedProduct t ∧
      (∀ x ∈ Icc 0 t, c.normalizedProduct x ≤ c.normalizedProduct t) ∧
      |c.signedCubicRatio t| ≤ 1/2+
        |materialSignedCurvature (c.position 0) c.period|/(2*c.rootBending t) := by
  let T' := max 0 T
  have hT : 0≤T' := le_max_left _ _
  obtain ⟨x,_,hx⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT)
    (c.normalizedProduct_continuousOn.mono (fun _ h => h.1))
  have hb : ¬c.HasBoundedEnergyLength := fun h => hnot ((c.quarter_length_iff_bounded_energyLength hf).mpr h)
  obtain ⟨t,ht,hm,hr⟩ := c.exists_record_above_of_unbounded hb (max K (c.normalizedProduct x)+1)
  have ht' : T'<t := by
    by_contra! hh
    have hbound : c.normalizedProduct t≤c.normalizedProduct x :=
      hx (show t∈Icc 0 T' from ⟨ht,hh⟩)
    linarith [le_max_right K (c.normalizedProduct x)]
  have ht0 := hT.trans_lt ht'
  refine ⟨t,(le_max_right 0 T).trans_lt ht',ht0,by linarith [le_max_left K (c.normalizedProduct x)],hr,?_⟩
  have h := c.signedCubicRatio_record hf ht0 hr
  have hden : 0<2*c.rootBending t := mul_pos (by norm_num) (c.rootBending_pos ht)
  apply (le_of_mul_le_mul_right ?_ hden)
  rw [add_mul,div_mul_cancel₀ _ hden.ne']
  linarith

theorem exists_late_high_record_below_cubic_half_add (hf : c.IsNormalFEF)
    (hnot : ¬ c.HasQuarterLengthBound) (K T : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ t, T<t ∧ K<c.normalizedProduct t ∧
      (∀ x ∈ Icc 0 t, c.normalizedProduct x ≤ c.normalizedProduct t) ∧
      |c.signedCubicRatio t|<1/2+ε := by
  let S := |materialSignedCurvature (c.position 0) c.period|
  obtain ⟨t,ht,ht0,hu,hr,hm⟩ := c.high_record_cubic_half_of_failure hf hnot
    (max K ((S/(2*ε))^2/2)) T
  have hK := lt_of_le_of_lt (le_max_left K _) hu
  refine ⟨t,ht,hK,hr,hm.trans_lt (add_lt_add_right ?_ _)⟩
  have hR := c.rootBending_pos ht0.le
  have hSq := c.rootBending_sq ht0.le
  have hRi : S/(2*ε)<c.rootBending t := by
    by_contra! hh
    have := pow_le_pow_left₀ hR.le hh 2
    linarith [lt_of_le_of_lt (le_max_right K _) hu]
  change S/(2*c.rootBending t)<ε
  apply (div_lt_iff₀ (by positivity)).mpr
  have := (div_lt_iff₀ (by positivity : 0<2*ε)).mp hRi
  linarith

end LengthGrowth.ActualFlow.ForwardImmersion

open Lean Elab Command in
run_cmd do
  for n in #[`LengthGrowth.ActualFlow.ForwardImmersion.centered_cubic_deficit,
      `LengthGrowth.ActualFlow.ForwardImmersion.normalized_cubic_deficit_bound,
      `LengthGrowth.ActualFlow.ForwardImmersion.supercritical_product_barrier,
      `LengthGrowth.ActualFlow.ForwardImmersion.quarter_bounds_of_eventual_supercritical_cubic,
      `LengthGrowth.ActualFlow.ForwardImmersion.quarter_bounds_of_liminf_cubic_gt_half,
      `LengthGrowth.ActualFlow.ForwardImmersion.high_record_cubic_half_of_failure,
      `LengthGrowth.ActualFlow.ForwardImmersion.exists_late_high_record_below_cubic_half_add] do
    for a in (← collectAxioms n) do
      unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains a do
        throwError "Unexpected axiom {a} in {n}"
  logInfo "CUBIC_HALF_THRESHOLD_AUDIT seven public results with standard axioms"
