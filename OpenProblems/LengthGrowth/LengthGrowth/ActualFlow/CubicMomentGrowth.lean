import LengthGrowth.ActualFlow.ConvexAreaEnergy
import LengthGrowth.ActualFlow.NormalizedProduct

/-! A signed cubic moment and a sufficient pointwise half-RMS curvature
condition for energy-length monotonicity of the actual free elastic flow. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ActualFlow

private theorem weighted_half_rms {k g : ℝ → ℝ} {P R : ℝ}
    (hP : 0 ≤ P) (hk : Continuous k) (hg : Continuous g) (hg0 : ∀ u, 0 ≤ g u)
    (hR : (∫ u in 0..P, k u ^ 2 * g u) = R ^ 2 * ∫ u in 0..P, g u)
    (hs : ∀ u, -R / 2 ≤ k u) :
    R ^ 3 * (∫ u in 0..P, g u) ≤ ∫ u in 0..P, k u ^ 3 * g u := by
  have hn : 0 ≤ ∫ u in 0..P, ((k u + R/2) * (k u - R)^2) * g u :=
    intervalIntegral.integral_nonneg_of_forall hP (fun u =>
      mul_nonneg (mul_nonneg (by linarith [hs u]) (sq_nonneg _)) (hg0 u))
  have h₂ : Continuous (fun u => k u ^ 2 * g u) := (hk.pow 2).mul hg
  have h₃ : Continuous (fun u => k u ^ 3 * g u) := (hk.pow 3).mul hg
  have hdiff : Continuous (fun u => k u ^ 3 * g u - (3*R/2) * (k u ^ 2 * g u)) :=
    h₃.sub (h₂.const_mul (3*R/2))
  have he : (∫ u in 0..P, ((k u + R/2) * (k u - R)^2) * g u) =
      (∫ u in 0..P, k u ^ 3 * g u) -
       (3*R/2) * (∫ u in 0..P, k u ^ 2 * g u) + (R^3/2) * ∫ u in 0..P, g u := by
    calc
      _ = ∫ u in 0..P, (k u ^ 3 * g u - (3*R/2) * (k u ^ 2 * g u)) +
          (R^3/2) * g u := by
        apply intervalIntegral.integral_congr
        intro u _
        dsimp only
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add
          (hdiff.intervalIntegrable 0 P)
          ((hg.const_mul (R^3/2)).intervalIntegrable 0 P),
          intervalIntegral.integral_sub (h₃.intervalIntegrable 0 P)
          ((h₂.const_mul (3*R/2)).intervalIntegrable 0 P),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [he, hR] at hn
  linarith

namespace ForwardImmersion
variable (c : ForwardImmersion)

def rmsCurvature (t : ℝ) : ℝ := Real.sqrt (2 * c.energy t / c.length t)

/-- This uses signed curvature. Positive and negative regions can cancel. -/
def CubicMomentDominates (t : ℝ) : Prop :=
  (2 * c.energy t)^3 ≤ c.length t * materialCubicCurvature (c.position t) c.period ^ 2

def OneSidedHalfRMS (t : ℝ) : Prop :=
  (∀ u, -(c.rmsCurvature t)/2 ≤ curvature (c.position t) u) ∨
    (∀ u, curvature (c.position t) u ≤ (c.rmsCurvature t)/2)

theorem cubicMomentDominates_of_oneSidedHalfRMS {t : ℝ} (ht : 0 ≤ t)
    (hs : c.OneSidedHalfRMS t) : c.CubicMomentDominates t := by
  let γ := c.position t
  let R := c.rmsCurvature t
  let L := c.length t
  let C := materialCubicCurvature γ c.period
  have hL : 0 < L := c.length_pos ht
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hE : 2 * c.energy t = R^2 * L := by
    dsimp only [R, rmsCurvature]
    rw [Real.sq_sqrt (div_nonneg (by have := c.energy_nonneg t; positivity) hL.le)]
    exact (div_mul_cancel₀ _ hL.ne').symm
  have hmean : (∫ u in 0..c.period, curvature γ u ^ 2 * speed γ u) =
      R ^ 2 * ∫ u in 0..c.period, speed γ u := by
    calc
      _ = 2 * c.energy t := by
        change (∫ u in 0..c.period, curvature γ u ^ 2 * speed γ u) =
          2 * ((1/2 : ℝ) * ∫ u in 0..c.period, curvature γ u ^ 2 * speed γ u)
        ring
      _ = _ := hE
  have hγ := c.position_slice_smooth ht
  have hr := c.immersion t ht
  have hk := (curvature_smooth hγ hr).continuous
  have hg := (speed_smooth hγ hr).continuous
  have hg0 (u : ℝ) : 0 ≤ speed γ u := (speed_pos hr u).le
  have hC : R ^ 3 * L ≤ |C| := by
    rcases hs with hp | hn
    · exact (weighted_half_rms c.period_pos.le hk hg hg0 hmean hp).trans (le_abs_self _)
    · have hm : (∫ u in 0..c.period, (-curvature γ u)^2 * speed γ u) =
          R ^ 2 * ∫ u in 0..c.period, speed γ u := by simpa only [neg_sq] using hmean
      have h := weighted_half_rms (k := fun u => -curvature γ u) c.period_pos.le hk.neg hg
        hg0 hm (fun u => by have := hn u; change -(c.rmsCurvature t)/2 ≤ -curvature (c.position t) u; linarith)
      have hid : (∫ u in 0..c.period, (-curvature γ u)^3 * speed γ u) = -C := by
        dsimp only [C, materialCubicCurvature]
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro u _
        dsimp only
        ring
      rw [hid] at h
      exact h.trans (neg_le_abs _)
  have hsquare := pow_le_pow_left₀ (mul_nonneg (pow_nonneg hR 3) hL.le) hC 2
  rw [sq_abs] at hsquare
  change (2*c.energy t)^3 ≤ L * C^2
  rw [hE]
  nlinarith only [mul_le_mul_of_nonneg_left hsquare hL.le]

theorem normalizedProduct_deriv_nonpos_of_cubicMoment (hf : c.IsNormalFEF)
    {t : ℝ} (ht : 0 < t) (hm : c.CubicMomentDominates t) :
    deriv c.normalizedProduct t ≤ 0 := by
  let E := c.energy t
  let L := c.length t
  let C := materialCubicCurvature (c.position t) c.period
  let D := c.dissipation t
  let v := c.lengthRate t
  have hl : 0 ≤ L := (c.length_pos ht.le).le
  have hd : 0 ≤ D := c.dissipation_nonneg t
  have hcs : C^2 ≤ 4*L*D := cubic_sq_le_four_length_dissipation c.period_pos.le
    (c.position_slice_smooth ht.le) (c.immersion t ht.le) (c.periodic t ht.le)
  have hv : v^2 ≤ 2*E*D := c.lengthRate_sq_le ht.le
  change (2*E)^3 ≤ L*C^2 at hm
  have h₁ : 2*E^3 ≤ L^2*D := by nlinarith only [hm, mul_le_mul_of_nonneg_left hcs hl]
  have h₂ : (E*v)^2 ≤ (L*D)^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hv (sq_nonneg E), mul_le_mul_of_nonneg_right h₁ hd]
  have h₃ : E*v ≤ L*D := by
    by_contra! hh
    nlinarith only [h₂, mul_self_lt_mul_self (mul_nonneg hl hd) hh]
  rw [(c.normalizedProduct_hasDerivAt_normal hf ht).deriv]
  exact sub_nonpos.mpr h₃

theorem normalizedProduct_antitoneOn_of_eventual_cubicMoment (hf : c.IsNormalFEF)
    {T : ℝ} (hT : 0 ≤ T) (hm : ∀ t ∈ Ioi T, c.CubicMomentDominates t) :
    AntitoneOn c.normalizedProduct (Ici T) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici T)
    (c.normalizedProduct_continuousOn.mono (fun _ hx => hT.trans hx))
  · rw [interior_Ici]
    intro t ht
    exact (c.normalizedProduct_hasDerivAt_normal hf
      (hT.trans_lt ht)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro t ht
    exact c.normalizedProduct_deriv_nonpos_of_cubicMoment hf (hT.trans_lt ht) (hm t ht)

theorem quarter_bounds_of_eventual_cubicMoment (hf : c.IsNormalFEF)
    {T : ℝ} (hT : 0 ≤ T) (hm : ∀ t ∈ Ioi T, c.CubicMomentDominates t) :
    c.HasQuarterLengthBound ∧ c.HasQuarterEnergyBound := by
  have ha := c.normalizedProduct_antitoneOn_of_eventual_cubicMoment hf hT hm
  obtain ⟨x, _, hx⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT)
    (c.normalizedProduct_continuousOn.mono (fun _ h => h.1))
  have hb : c.HasBoundedEnergyLength := by
    refine ⟨c.normalizedProduct x, fun t ht => ?_⟩
    by_cases hh : t ≤ T
    · exact hx ⟨ht, hh⟩
    · have htT : T ≤ t := le_of_not_ge hh
      exact (ha (show T ∈ Ici T from show T ≤ T from le_rfl) (show t ∈ Ici T from htT) htT).trans
        (hx ⟨hT, le_rfl⟩)
  have hl := (c.quarter_length_iff_bounded_energyLength hf).mpr hb
  exact ⟨hl, c.quarter_energy_of_quarter_length hf hl⟩

theorem quarter_bounds_of_eventual_oneSidedHalfRMS (hf : c.IsNormalFEF)
    {T : ℝ} (hT : 0 ≤ T) (hs : ∀ t ∈ Ioi T, c.OneSidedHalfRMS t) :
    c.HasQuarterLengthBound ∧ c.HasQuarterEnergyBound :=
  c.quarter_bounds_of_eventual_cubicMoment hf hT (fun t ht =>
    c.cubicMomentDominates_of_oneSidedHalfRMS (hT.trans ht.le) (hs t ht))

end ForwardImmersion
end LengthGrowth.ActualFlow

#print axioms LengthGrowth.ActualFlow.ForwardImmersion.normalizedProduct_antitoneOn_of_eventual_cubicMoment
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_bounds_of_eventual_oneSidedHalfRMS
