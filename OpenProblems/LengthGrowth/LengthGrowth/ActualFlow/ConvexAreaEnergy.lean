import LengthGrowth.ActualFlow.EventualCurvatureSign
import LengthGrowth.ActualFlow.SignedAreaVariation

/-! The Green-area/bending-energy monotonicity on actual moving curves.
The geometric Gage inequality for convex boundaries and their turning
integral are explicit hypotheses. The first variations and both integral
Cauchy--Schwarz bounds are proved internally. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ActualFlow

private theorem weighted_integral_cs {f g : ℝ → ℝ} {P : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hg0 : ∀ u, 0 ≤ g u) (hP : 0 ≤ P) :
    (∫ u in 0..P, f u * g u) ^ 2 ≤
      (∫ u in 0..P, g u) * ∫ u in 0..P, f u ^ 2 * g u := by
  have h := LengthGrowth.interval_integral_mul_sq_le hg.sqrt (hf.mul hg.sqrt) hP
  simp only [Pi.mul_apply] at h
  have h₁ : (fun u => Real.sqrt (g u) * (f u * Real.sqrt (g u))) =
      fun u => f u * g u := by
    funext u
    calc
      _ = f u * Real.sqrt (g u) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (hg0 u)]
  have h₂ : (fun u => Real.sqrt (g u) ^ 2) = g := by
    funext u
    exact Real.sq_sqrt (hg0 u)
  have h₃ : (fun u => (f u * Real.sqrt (g u)) ^ 2) =
      fun u => f u ^ 2 * g u := by
    funext u
    rw [mul_pow, Real.sq_sqrt (hg0 u)]
  rwa [h₁, h₂, h₃] at h

theorem curvature_cubic_moment {γ : ℝ → ℂ} {P : ℝ} (hP : 0 ≤ P)
    (hs : ContDiff ℝ ∞ γ) (hr : ∀ u, deriv γ u ≠ 0)
    (hk : ∀ u, 0 ≤ curvature γ u) :
    (2 * materialEnergy γ P) ^ 2 ≤
      materialSignedCurvature γ P * materialCubicCurvature γ P := by
  have hc := (curvature_smooth hs hr).continuous
  have hg := (speed_smooth hs hr).continuous
  have h := weighted_integral_cs (f := curvature γ) (g := fun u => curvature γ u * speed γ u)
    hc (hc.mul hg) (fun u => mul_nonneg (hk u) (speed_pos hr u).le) hP
  have h₁ : (fun u => curvature γ u * (curvature γ u * speed γ u)) =
      fun u => curvature γ u ^ 2 * speed γ u := by funext u; ring
  have h₂ : (fun u => curvature γ u ^ 2 * (curvature γ u * speed γ u)) =
      fun u => curvature γ u ^ 3 * speed γ u := by funext u; ring
  rw [h₁, h₂] at h
  dsimp only [materialEnergy, materialCubicCurvature, materialSignedCurvature]
  rw [← mul_assoc]
  norm_num
  exact h

theorem cubic_sq_le_four_length_dissipation {γ : ℝ → ℂ} {P : ℝ} (hP : 0 ≤ P)
    (hs : ContDiff ℝ ∞ γ) (hr : ∀ u, deriv γ u ≠ 0) (hp : Function.Periodic γ P) :
    materialCubicCurvature γ P ^ 2 ≤ 4 * materialLength γ P * materialDissipation γ P := by
  have h := weighted_integral_cs (force_smooth hs hr).continuous (speed_smooth hs hr).continuous
    (fun u => (speed_pos hr u).le) hP
  rw [integral_force_eq_half_cubic hs hr hp] at h
  change ((1 / 2 : ℝ) * materialCubicCurvature γ P) ^ 2 ≤
    materialLength γ P * materialDissipation γ P at h
  nlinarith only [h]

namespace ForwardImmersion
variable (c : ForwardImmersion)

def areaEnergy (t : ℝ) : ℝ := materialSignedArea (c.position t) c.period * c.energy t ^ 2

theorem signedArea_continuousOn :
    ContinuousOn (fun x => materialSignedArea (c.position x) c.period) (Ici 0) := by
  have hp : ContinuousOn (fun z : ℝ × ℝ => c.position z.1 z.2) (Ici 0 ×ˢ univ) := by
    simpa only [iteratedDeriv_zero] using c.spatial_jets_continuous 0 (by norm_num)
  exact continuousOn_intervalIntegral_forward
    (((Complex.continuous_re.comp_continuousOn hp).mul
      (Complex.continuous_im.comp_continuousOn c.jet1_continuousOn)).mono
      (fun _ hz => ⟨hz.1, mem_univ _⟩))

theorem areaEnergy_hasDerivAt (hf : c.IsNormalFEF) {t : ℝ} (ht : 0 < t) :
    HasDerivAt c.areaEnergy (c.energy t / 2 *
      (c.energy t * materialCubicCurvature (c.position t) c.period -
      4 * materialSignedArea (c.position t) c.period * c.dissipation t)) t := by
  convert! (c.signedArea_hasDerivAt_normal hf ht).mul
    (c.energy_sq_hasDerivAt_normal hf ht) using 1
  ring

/-- Here Gage is stated as π L ≤ 2 A E, with the turning number specified
by the actual integral of signed curvature. -/
theorem areaEnergy_deriv_nonpos_of_gage (hf : c.IsNormalFEF) {t : ℝ} (ht : 0 < t)
    (hk : ∀ u, 0 ≤ curvature (c.position t) u)
    (hturn : materialSignedCurvature (c.position t) c.period = 2 * Real.pi)
    (hGage : Real.pi * c.length t ≤
      2 * materialSignedArea (c.position t) c.period * c.energy t) :
    deriv c.areaEnergy t ≤ 0 := by
  let A := materialSignedArea (c.position t) c.period
  let C := materialCubicCurvature (c.position t) c.period
  let E := c.energy t
  let L := c.length t
  let D := c.dissipation t
  have hl : 0 < L := c.length_pos ht.le
  have he : 0 < E := c.energy_pos ht.le
  have hg : Real.pi * L ≤ 2 * A * E := hGage
  have hA : 0 ≤ A := by
    by_contra! hn
    nlinarith only [hg, mul_pos Real.pi_pos hl, mul_neg_of_neg_of_pos hn he]
  have hc : 0 ≤ C := intervalIntegral.integral_nonneg_of_forall c.period_pos.le
    (fun u => mul_nonneg (pow_nonneg (hk u) _) (speed_pos (c.immersion t ht.le) u).le)
  have hm := curvature_cubic_moment c.period_pos.le (c.position_slice_smooth ht.le)
    (c.immersion t ht.le) hk
  rw [hturn] at hm
  change (2 * E) ^ 2 ≤ 2 * Real.pi * C at hm
  have hd : C ^ 2 ≤ 4 * L * D :=
    cubic_sq_le_four_length_dissipation c.period_pos.le (c.position_slice_smooth ht.le)
      (c.immersion t ht.le) (c.periodic t ht.le)
  have hle : E * L ≤ A * C := by
    apply le_of_mul_le_mul_left (a := Real.pi) _ Real.pi_pos
    nlinarith only [mul_le_mul_of_nonneg_right hg he.le, mul_le_mul_of_nonneg_left hm hA]
  have hlast : E * C ≤ 4 * A * D := by
    apply le_of_mul_le_mul_left (a := L) _ hl
    nlinarith only [mul_le_mul_of_nonneg_right hle hc, mul_le_mul_of_nonneg_left hd hA]
  rw [(c.areaEnergy_hasDerivAt hf ht).deriv]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hlast)

theorem areaEnergy_antitoneOn_of_gage (hf : c.IsNormalFEF) {T : ℝ} (hT : 0 ≤ T)
    (hk : ∀ t ∈ Ioi T, ∀ u, 0 ≤ curvature (c.position t) u)
    (hturn : materialSignedCurvature (c.position 0) c.period = 2 * Real.pi)
    (hGage : ∀ t ∈ Ioi T, Real.pi * c.length t ≤
      2 * materialSignedArea (c.position t) c.period * c.energy t) :
    AntitoneOn c.areaEnergy (Ici T) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici T)
    ((c.signedArea_continuousOn.mul (c.energy_continuousOn.pow 2)).mono
      (fun _ hx => hT.trans hx))
  · rw [interior_Ici]
    intro t ht
    exact (c.areaEnergy_hasDerivAt hf (hT.trans_lt ht)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro t ht
    exact c.areaEnergy_deriv_nonpos_of_gage hf (hT.trans_lt ht) (hk t ht)
      ((c.signedCurvature_eq_initial (hT.trans ht.le)).trans hturn) (hGage t ht)

end ForwardImmersion
end LengthGrowth.ActualFlow

#print axioms LengthGrowth.ActualFlow.ForwardImmersion.areaEnergy_antitoneOn_of_gage
