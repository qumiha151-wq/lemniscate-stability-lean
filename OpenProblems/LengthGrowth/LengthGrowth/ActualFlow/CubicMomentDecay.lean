import LengthGrowth.ActualFlow.CubicMomentDissipation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Quantitative curvature-oscillation decay from the signed cubic
moment on a tail of an actual smooth normal flow. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- Constant extension to negative times makes the primitive globally defined.
On the physical domain this equals (2E)^2/(8 L^2). -/
def oscillationDecayRate (t : ℝ) : ℝ :=
  (2 * c.energy (max 0 t))^2 / (8 * c.length (max 0 t)^2)

theorem oscillationDecayRate_continuous : Continuous c.oscillationDecayRate := by
  have hc : Continuous (fun t : ℝ => max 0 t) := continuous_const.max continuous_id
  have he : Continuous (fun t : ℝ => c.energy (max 0 t)) :=
    c.energy_continuousOn.comp_continuous hc (fun t => show 0 ≤ max 0 t from le_max_left 0 t)
  have hl : Continuous (fun t : ℝ => c.length (max 0 t)) :=
    c.length_continuousOn.comp_continuous hc (fun t => show 0 ≤ max 0 t from le_max_left 0 t)
  exact ((he.const_mul 2).pow 2).div ((hl.pow 2).const_mul 8) (by
    intro t
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (c.length_pos (le_max_left 0 t)).ne'))

theorem oscillationDecayRate_forward {t : ℝ} (ht : 0 ≤ t) :
    c.oscillationDecayRate t = (2*c.energy t)^2/(8*c.length t^2) := by
  simp [oscillationDecayRate, max_eq_right ht]

theorem curvatureOscillation_continuousOn :
    ContinuousOn c.curvatureOscillation (Ici 0) :=
  (c.normalizedProduct_continuousOn.const_mul 2).sub continuousOn_const

theorem curvatureOscillation_le_exp_integral (hf : c.IsNormalFEF) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t)
    (hm : ∀ x ∈ Ioo s t, c.CubicMomentDominates x) :
    c.curvatureOscillation t ≤ c.curvatureOscillation s *
      Real.exp (-(∫ x in s..t, c.oscillationDecayRate x)) := by
  let J (x : ℝ) := ∫ y in s..x, c.oscillationDecayRate y
  have hr := c.oscillationDecayRate_continuous
  have hJ (x : ℝ) : HasDerivAt J (c.oscillationDecayRate x) x :=
    intervalIntegral.integral_hasDerivAt_right (hr.intervalIntegrable ..)
      hr.stronglyMeasurable.stronglyMeasurableAtFilter hr.continuousAt
  have hJc : Continuous J := continuous_iff_continuousAt.mpr fun x => (hJ x).continuousAt
  have hQ : ContinuousOn c.curvatureOscillation (Icc s t) :=
    c.curvatureOscillation_continuousOn.mono (fun _ hx => hs.trans hx.1)
  let W (x : ℝ) := Real.exp (J x) * c.curvatureOscillation x
  have hwd {x : ℝ} (hx : 0 < x) :
      HasDerivAt W (Real.exp (J x) * c.oscillationDecayRate x * c.curvatureOscillation x +
        Real.exp (J x) * deriv c.curvatureOscillation x) x := by
    have h := ((hJ x).exp).mul (c.curvatureOscillation_hasDerivAt hf hx)
    rw [(c.curvatureOscillation_hasDerivAt hf hx).deriv]
    convert! h using 1
  have hanti : AntitoneOn W (Icc s t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc s t)
      ((Real.continuous_exp.comp hJc).continuousOn.mul hQ)
    · rw [interior_Icc]
      intro x hx
      exact (hwd (hs.trans_lt hx.1)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      have hx0 := hs.trans_lt hx.1
      have hd := c.curvatureOscillation_deriv_bound hf hx0 (hm x hx)
      have hl := c.length_pos hx0.le
      have ha : c.oscillationDecayRate x * c.curvatureOscillation x +
          deriv c.curvatureOscillation x ≤ 0 := by
        rw [c.oscillationDecayRate_forward hx0.le]
        apply (le_of_mul_le_mul_left (a := 8*c.length x^2) _ (by positivity))
        field_simp [hl.ne']
        nlinarith only [hd]
      change deriv W x ≤ 0
      rw [(hwd hx0).deriv]
      nlinarith only [mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (J x)).le ha]
  have hw := hanti (show s ∈ Icc s t from ⟨le_rfl, hst⟩)
    (show t ∈ Icc s t from ⟨hst, le_rfl⟩) hst
  change Real.exp (J t) * c.curvatureOscillation t ≤ Real.exp (J s) * c.curvatureOscillation s at hw
  simp only [J, intervalIntegral.integral_same, Real.exp_zero, one_mul] at hw
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using hw)

theorem inverse_fourth_le_oscillationDecayRate {t : ℝ} (ht : 0 ≤ t) :
    1/(8*c.length t^4) ≤ c.oscillationDecayRate t := by
  have hs := c.absoluteCurvature_sq_le ht
  have ha := c.absoluteCurvature_lower ht
  have hb : 1 ≤ 2*c.energy t*c.length t := by nlinarith only [hs, ha, sq_nonneg (c.absoluteCurvature t-1)]
  have hl := c.length_pos ht
  rw [c.oscillationDecayRate_forward ht]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hb 2)
    (sq_nonneg (c.length t))]

theorem curvatureOscillation_le_exp_rescaled_time (hf : c.IsNormalFEF) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (hm : ∀ x ∈ Ioo s t, c.CubicMomentDominates x) :
    c.curvatureOscillation t ≤ c.curvatureOscillation s *
      Real.exp (-(∫ x in s..t, 1 / c.length x^4)/8) := by
  have hc : ContinuousOn (fun x => 1/(8*c.length x^4)) (Icc s t) :=
    continuousOn_const.div ((c.length_continuousOn.pow 4).const_mul 8 |>.mono
      (fun _ hx => hs.trans hx.1)) (fun _ hx =>
        mul_ne_zero (by norm_num) (pow_ne_zero 4 (c.length_pos (hs.trans hx.1)).ne'))
  have h := intervalIntegral.integral_mono_on (μ := volume) hst (hc.intervalIntegrable_of_Icc hst)
    (c.oscillationDecayRate_continuous.intervalIntegrable ..)
    (fun x hx => c.inverse_fourth_le_oscillationDecayRate (hs.trans hx.1))
  have he : (∫ x in s..t, 1/(8*c.length x^4)) =
      (1/8 : ℝ)*(∫ x in s..t, 1/c.length x^4) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    simp [div_eq_mul_inv, mul_inv_rev, mul_comm]
  rw [he] at h
  apply (c.curvatureOscillation_le_exp_integral hf hs hst hm).trans
  apply mul_le_mul_of_nonneg_left _ (c.curvatureOscillation_nonneg hs)
  apply Real.exp_le_exp.mpr
  linarith

theorem oscillationDecayRate_integral_lower {a s t : ℝ} (ha : 0 < a)
    (hL : ∀ x, 0 ≤ x → c.length x ≤ a * FreeElasticScalar.fourthRoot (1+x))
    (hs : 0 ≤ s) (hst : s ≤ t) :
    (Real.log (1+t)-Real.log (1+s))/(8*a^4) ≤ ∫ x in s..t, c.oscillationDecayRate x := by
  let w (x : ℝ) := 1/(8*a^4*(1+x))
  have hc : ContinuousOn w (Icc s t) := by
    apply continuousOn_const.div (continuous_const.mul (continuous_const.add continuous_id)).continuousOn
    intro x hx
    have hb : 0 < 1+x := by linarith [hs.trans hx.1]
    exact mul_ne_zero (by positivity) hb.ne'
  have hW {x : ℝ} (hx : s ≤ x) :
      HasDerivAt (fun y : ℝ => Real.log (1+y)/(8*a^4)) (w x) x := by
    have hb : 0 < 1+x := by linarith
    have h := (((hasDerivAt_id x).const_add 1).log hb.ne').div_const (8*a^4)
    convert! h using 1
    dsimp [w]
    field_simp [ha.ne', hb.ne']
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun y : ℝ =>
    Real.log (1+y)/(8*a^4)) hst (fun x hx => (hW hx.1).continuousAt.continuousWithinAt)
    (fun x hx => hW hx.1.le) (hc.intervalIntegrable_of_Icc hst)
  have hm : (∫ x in s..t, w x) ≤ ∫ x in s..t, c.oscillationDecayRate x := by
    apply intervalIntegral.integral_mono_on hst (hc.intervalIntegrable_of_Icc hst)
      (c.oscillationDecayRate_continuous.intervalIntegrable ..)
    intro x hx
    have hx0 := hs.trans hx.1
    have hx1 : 0 < 1+x := by linarith
    have hl := c.length_pos hx0
    have h₄ := pow_le_pow_left₀ hl.le (hL x hx0) 4
    rw [mul_pow, FreeElasticScalar.fourthRoot_pow_four hx1.le] at h₄
    apply le_trans _ (c.inverse_fourth_le_oscillationDecayRate hx0)
    apply (div_le_div_iff₀ (by positivity : 0 < 8*a^4*(1+x)) (by positivity)).mpr
    nlinarith only [h₄]
  rw [he] at hm
  exact (le_of_eq (sub_div ..)).trans hm

theorem curvatureOscillation_tendsto_zero_of_eventual_cubicMoment (hf : c.IsNormalFEF)
    {T : ℝ} (hT : 0 ≤ T) (hm : ∀ t ∈ Ioi T, c.CubicMomentDominates t) :
    Tendsto c.curvatureOscillation atTop (𝓝 0) := by
  obtain ⟨a, ha, hL⟩ := (c.quarter_bounds_of_eventual_cubicMoment hf hT hm).1
  have htime : Tendsto (fun t : ℝ => 1+t) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_id
  have hlog := Real.tendsto_log_atTop.comp htime
  have hsub : Tendsto (fun t : ℝ => Real.log (1+t) - Real.log (1+T)) atTop atTop := by
    simpa only [sub_eq_add_neg, Function.comp_apply] using
      tendsto_atTop_add_const_right _ (-(Real.log (1+T))) hlog
  have hj : Tendsto (fun t : ℝ => ∫ x in T..t, c.oscillationDecayRate x) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (hsub.atTop_div_const (show 0 < 8*a^4 by positivity))
    filter_upwards [eventually_ge_atTop T] with t ht
    exact c.oscillationDecayRate_integral_lower ha hL hT ht
  have hz := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hj)).const_mul
    (c.curvatureOscillation T)
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact c.curvatureOscillation_nonneg ht
  · filter_upwards [eventually_ge_atTop T] with t ht
    exact c.curvatureOscillation_le_exp_integral hf hT ht (fun x hx => hm x hx.1)
  · simpa only [mul_zero, Function.comp_apply] using hz

theorem signedCurvature_sq_ge_one_of_eventual_cubicMoment (hf : c.IsNormalFEF)
    {T : ℝ} (hT : 0 ≤ T) (hm : ∀ t ∈ Ioi T, c.CubicMomentDominates t) :
    1 ≤ materialSignedCurvature (c.position 0) c.period ^ 2 := by
  let S := materialSignedCurvature (c.position 0) c.period
  have hk := c.curvatureOscillation_tendsto_zero_of_eventual_cubicMoment hf hT hm
  have hlim : Tendsto (fun t => c.curvatureOscillation t + S^2) atTop (𝓝 (S^2)) := by
    simpa only [zero_add] using hk.add_const (S^2)
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have h₁ := c.absoluteCurvature_sq_le ht
  have h₂ := c.absoluteCurvature_lower ht
  change 1 ≤ 2 * (c.energy t*c.length t) - S^2 + S^2
  nlinarith only [h₁, h₂, sq_nonneg (c.absoluteCurvature t-1)]

end LengthGrowth.ActualFlow.ForwardImmersion

#print axioms LengthGrowth.ActualFlow.ForwardImmersion.curvatureOscillation_le_exp_integral
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.curvatureOscillation_le_exp_rescaled_time
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.curvatureOscillation_tendsto_zero_of_eventual_cubicMoment
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.signedCurvature_sq_ge_one_of_eventual_cubicMoment
