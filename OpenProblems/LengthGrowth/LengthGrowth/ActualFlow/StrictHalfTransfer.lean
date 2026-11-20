import LengthGrowth.ActualFlow.CubicHalfThreshold
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! From the strict static cubic-moment gap to both forward-flow
consequences. The universal spatial estimate is an explicit premise on
individual immersed positions; it contains no time derivatives or flows. -/
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow

/-- The RMS-normalised static estimate, written in the original material
integrals. Multiplying the normalised loss by b³ restores L⁴(LD−EV). -/
def StrictHalfSliceGap (ε : ℝ) : Prop :=
  ∀ γ : PeriodicRegularPosition,
    let L := materialLength γ.position γ.period
    let E := materialEnergy γ.position γ.period
    let D := materialDissipation γ.position γ.period
    let V := materialLengthRate γ.position γ.period
    let C := materialCubicCurvature γ.position γ.period
    let S := materialSignedCurvature γ.position γ.period
    let b := 2*(E*L)
    |S| / Real.sqrt b ≤ ε → L^4*(L*D-E*V) ≤ ε*b^3 →
      |L*C/(2*E*Real.sqrt b)| ≤ 1/2-ε

namespace ForwardImmersion
variable (c : ForwardImmersion)

private theorem loss_at_high_cubic {ε t : ℝ} (gap : StrictHalfSliceGap ε) (ht : 0≤t)
    (hS : |materialSignedCurvature (c.position 0) c.period|/c.rootBending t ≤ ε)
    (hG : 1/2-ε < |c.signedCubicRatio t|) :
    ε*(2*c.normalizedProduct t)^3 <
      c.length t^4*(c.length t*c.dissipation t-c.energy t*c.lengthRate t) := by
  apply lt_of_not_ge
  intro h
  apply (not_le_of_gt hG)
  apply gap (c.regularPositionAt ht)
  · change |materialSignedCurvature (c.position t) c.period|/c.rootBending t ≤ ε
    rwa [c.signedCurvature_eq_initial ht]
  · exact h

private theorem derivative_at_record_nonneg (hf : c.IsNormalFEF) {t : ℝ} (ht : 0<t)
    (hr : ∀ x ∈ Icc 0 t, c.normalizedProduct x ≤ c.normalizedProduct t) :
    0 ≤ c.energy t*c.lengthRate t-c.length t*c.dissipation t := by
  have hs := (hasDerivAt_iff_tendsto_slope_left_right.mp
    (c.normalizedProduct_hasDerivAt_normal hf ht)).1
  apply ge_of_tendsto hs
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds ht)] with x hx hx0
  rw [slope_def_field]
  exact div_nonneg_of_nonpos (sub_nonpos.mpr (hr x ⟨hx0.le,hx.le⟩)) (sub_nonpos.mpr hx.le)

/-- The static gap forbids arbitrarily large product records on a
high-moment tail, giving both quarter-power bounds for the actual flow. -/
theorem quarter_bounds_of_strict_half_tail (hf : c.IsNormalFEF) {ε : ℝ} (hε : 0<ε)
    (gap : StrictHalfSliceGap ε) (tail : ∀ᶠ t : ℝ in atTop, 1/2-ε < |c.signedCubicRatio t|) :
    c.HasQuarterLengthBound ∧ c.HasQuarterEnergyBound := by
  suffices hL : c.HasQuarterLengthBound from ⟨hL,c.quarter_energy_of_quarter_length hf hL⟩
  by_contra hnot
  obtain ⟨T,hT⟩ := eventually_atTop.1 tail
  let S := |materialSignedCurvature (c.position 0) c.period|
  obtain ⟨t,hTt,ht,hU,hr,_⟩ := c.high_record_cubic_half_of_failure hf hnot ((S/ε)^2/2) T
  have hR : 0<c.rootBending t := Real.sqrt_pos_of_pos (by
    change 0<2*(c.energy t*c.length t)
    have := c.energy_pos ht.le
    have := c.length_pos ht.le
    positivity)
  have hturn : S/c.rootBending t ≤ ε := by
    apply (div_le_iff₀ hR).mpr
    by_contra! hh
    have hsmall : c.rootBending t ≤ S/ε := (le_div_iff₀ hε).mpr (by linarith)
    have hsq := pow_le_pow_left₀ hR.le hsmall 2
    rw [c.rootBending_sq ht.le] at hsq
    linarith
  have loss := c.loss_at_high_cubic gap ht.le hturn (hT t hTt.le)
  have hr' := c.derivative_at_record_nonneg hf ht hr
  have neg : c.length t*c.dissipation t-c.energy t*c.lengthRate t ≤ 0 := by linarith
  have base := c.normalizedProduct_nonneg t
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (by positivity) neg))
    (lt_of_le_of_lt (by positivity) loss)

/-- The extended-real liminf may be infinite. -/
theorem quarter_bounds_of_strict_half_liminf (hf : c.IsNormalFEF) {ε : ℝ} (hε : 0<ε)
    (gap : StrictHalfSliceGap ε)
    (h : ((1/2-ε : ℝ) : EReal) < liminf (fun t : ℝ => ((|c.signedCubicRatio t| : ℝ) : EReal)) atTop) :
    c.HasQuarterLengthBound ∧ c.HasQuarterEnergyBound :=
  c.quarter_bounds_of_strict_half_tail hf hε gap
    ((eventually_lt_of_lt_liminf h).mono (fun _ ht => EReal.coe_lt_coe_iff.mp ht))

/-- At zero signed turning a high-cubic tail would expend an infinite
amount of a nonnegative energy-length product, by logarithmic comparison. -/
theorem zero_turn_liminf_le_strict_half (hf : c.IsNormalFEF) {ε : ℝ} (hε : 0<ε)
    (gap : StrictHalfSliceGap ε) (zeroTurn : materialSignedCurvature (c.position 0) c.period=0) :
    liminf (fun t : ℝ => ((|c.signedCubicRatio t| : ℝ) : EReal)) atTop ≤ ((1/2-ε : ℝ) : EReal) := by
  by_contra! h
  have tail : ∀ᶠ t : ℝ in atTop, 1/2-ε < |c.signedCubicRatio t| :=
    (eventually_lt_of_lt_liminf h).mono (fun _ ht => EReal.coe_lt_coe_iff.mp ht)
  obtain ⟨a,ha,hL⟩ := (c.quarter_bounds_of_strict_half_tail hf hε gap tail).1
  obtain ⟨T,hT⟩ := eventually_atTop.1 tail
  let start := max 0 T
  have hs : 0≤start := le_max_left _ _
  let A := ε/a^4
  have hA : 0<A := div_pos hε (pow_pos ha _)
  let W := fun t : ℝ => c.normalizedProduct t + A*Real.log (1+t)
  have hcont : ContinuousOn W (Ici start) := by
    apply (c.normalizedProduct_continuousOn.mono (fun _ hx => hs.trans hx)).add
    apply continuousOn_const.mul ((continuous_const.add continuous_id).continuousOn.log ?_)
    intro x hx
    change 1+x ≠ 0
    linarith [show start≤x from hx]
  have hd {x : ℝ} (hx : start<x) : HasDerivAt W
      (c.energy x*c.lengthRate x-c.length x*c.dissipation x + A/(1+x)) x := by
    have h := (((hasDerivAt_id x).const_add 1).log (by linarith : 1+x≠0)).const_mul A
    convert! (c.normalizedProduct_hasDerivAt_normal hf (hs.trans_lt hx)).add h using 1
    simp [div_eq_mul_inv]
  have nonpos {x : ℝ} (hx : start<x) :
      c.energy x*c.lengthRate x-c.length x*c.dissipation x+A/(1+x) ≤ 0 := by
    have hx0 := hs.trans hx.le
    have hx1 : 0<1+x := by linarith
    have loss := c.loss_at_high_cubic gap hx0
      (by simp [zeroTurn,hε.le]) (hT x ((le_max_right 0 T).trans hx.le))
    have b : 1 ≤ 2*c.normalizedProduct x := by
      change 1 ≤ 2*(c.energy x*c.length x)
      have h₁ := c.absoluteCurvature_sq_le hx0
      have h₂ := c.absoluteCurvature_lower hx0
      nlinarith only [h₁,h₂,sq_nonneg (c.absoluteCurvature x-1)]
    have b3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) b 3
    have positive : ε < c.length x^4*(c.length x*c.dissipation x-c.energy x*c.lengthRate x) :=
      lt_of_le_of_lt (by simpa using mul_le_mul_of_nonneg_left b3 hε.le) loss
    have hb : 0 ≤ c.length x*c.dissipation x-c.energy x*c.lengthRate x :=
      le_of_lt (pos_of_mul_pos_right (hε.trans positive) (by positivity))
    have h4 := pow_le_pow_left₀ (c.length_pos hx0).le (hL x hx0) 4
    rw [mul_pow,FreeElasticScalar.fourthRoot_pow_four hx1.le] at h4
    have hproduct := positive.le.trans (mul_le_mul_of_nonneg_right h4 hb)
    have hquot : A/(1+x) ≤ c.length x*c.dissipation x-c.energy x*c.lengthRate x := by
      dsimp [A]
      rw [div_div]
      apply (div_le_iff₀ (mul_pos (pow_pos ha _) hx1)).mpr
      linarith only [hproduct]
    linarith only [hquot]
  have dec : AntitoneOn W (Ici start) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) hcont
    · rw [interior_Ici]
      intro x hx
      exact (hd hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro x hx
      rw [(hd hx).deriv]
      exact nonpos hx
  have hlog : Tendsto (fun t : ℝ => Real.log (1+t)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left _ _ tendsto_id)
  obtain ⟨t,ht,hlarge⟩ := ((eventually_ge_atTop start).and
    (hlog.eventually_gt_atTop (W start/A))).exists
  have high := (div_lt_iff₀ hA).mp hlarge
  have bound := dec (Set.mem_Ici.mpr (le_rfl : start≤start)) (Set.mem_Ici.mpr ht) ht
  change c.normalizedProduct t+A*Real.log (1+t) ≤ W start at bound
  nlinarith only [high,bound,c.normalizedProduct_nonneg t]

/-- The same uniform spatial gap supplies one threshold strictly below
one half for every forward immersion solving the normal free elastic flow. -/
theorem exists_universal_strict_half_flow_threshold
    (spatial : ∃ ε : ℝ, 0<ε ∧ ε<1/2 ∧ StrictHalfSliceGap ε) :
    ∃ g : ℝ, 0<g ∧ g<1/2 ∧ ∀ c : ForwardImmersion, c.IsNormalFEF →
      ((((g:EReal) < liminf (fun t : ℝ => ((|c.signedCubicRatio t|:ℝ):EReal)) atTop) →
        c.HasQuarterLengthBound ∧ c.HasQuarterEnergyBound) ∧
       (materialSignedCurvature (c.position 0) c.period=0 →
        liminf (fun t : ℝ => ((|c.signedCubicRatio t|:ℝ):EReal)) atTop ≤ (g:EReal))) := by
  obtain ⟨ε,hε,hu,hgap⟩ := spatial
  refine ⟨1/2-ε,by linarith,by linarith,fun c hf => ?_⟩
  exact ⟨c.quarter_bounds_of_strict_half_liminf hf hε hgap,
    c.zero_turn_liminf_le_strict_half hf hε hgap⟩

end ForwardImmersion
end LengthGrowth.ActualFlow

open Lean Elab Command in
run_cmd do
  let names := #[`LengthGrowth.ActualFlow.ForwardImmersion.quarter_bounds_of_strict_half_tail,
    `LengthGrowth.ActualFlow.ForwardImmersion.quarter_bounds_of_strict_half_liminf,
    `LengthGrowth.ActualFlow.ForwardImmersion.zero_turn_liminf_le_strict_half,
    `LengthGrowth.ActualFlow.ForwardImmersion.exists_universal_strict_half_flow_threshold]
  for name in names do
    for ax in (← collectAxioms name) do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
  logInfo "STRICT_HALF_TRANSFER actual FEF: quarter length and energy, zero-turn liminf, uniform threshold."
