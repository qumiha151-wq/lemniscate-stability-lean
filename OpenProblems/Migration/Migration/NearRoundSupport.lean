import Migration.NearRoundCentroid

/-! A position-defined support estimate for closed immersed slices, in the
material parameter. The normal hitting a specified support direction is
explicit, so the lemma applies independently of how turning is certified. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion

private theorem bounded_difference {z dz : ℝ → ℝ} {P x y : ℝ}
    (hd : ∀ u, HasDerivAt z (dz u) u) (hc : Continuous dz)
    (hx : x ∈ Icc 0 P) (hy : y ∈ Icc 0 P) :
    |z x - z y| ≤ ∫ u in 0..P, |dz u| := by
  have hforward (a b : ℝ) (ha : a ∈ Icc 0 P) (hb : b ∈ Icc 0 P) (hab : a ≤ b) :
      |z b - z a| ≤ ∫ u in 0..P, |dz u| := by
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
      (hc.intervalIntegrable a b)]
    exact (intervalIntegral.abs_integral_le_integral_abs hab).trans
      (intervalIntegral.integral_mono_interval ha.1 hab hb.2
        (.of_forall fun u => abs_nonneg (dz u)) (hc.abs.intervalIntegrable _ _))
  rcases le_total x y with hxy | hyx
  · rw [abs_sub_comm]
    exact hforward x y hx hy hxy
  · exact hforward y x hy hx hyx

private theorem centered_oscillation {z dz g : ℝ → ℝ} {P x : ℝ}
    (hd : ∀ u, HasDerivAt z (dz u) u) (hc : Continuous dz) (hg : Continuous g)
    (hg0 : ∀ u, 0 ≤ g u) (hL : 0 < ∫ u in 0..P, g u)
    (hm : (∫ u in 0..P, z u * g u) = 0) (hx : x ∈ Icc 0 P) :
    |z x| ≤ ∫ u in 0..P, |dz u| := by
  let a := ∫ u in 0..P, |dz u|
  have hz : Continuous z := continuous_iff_continuousAt.mpr fun u => (hd u).continuousAt
  have hdif (u : ℝ) (hu : u ∈ Icc 0 P) := abs_le.mp (bounded_difference hd hc hx hu)
  have lower := intervalIntegral.integral_mono_on (μ := volume) (hx.1.trans hx.2)
    ((hg.const_mul (z x-a)).intervalIntegrable _ _) ((hz.mul hg).intervalIntegrable _ _)
    (fun u hu => mul_le_mul_of_nonneg_right (by linarith [(hdif u hu).2] : z x-a ≤ z u) (hg0 u))
  have upper := intervalIntegral.integral_mono_on (μ := volume) (hx.1.trans hx.2)
    ((hz.mul hg).intervalIntegrable _ _) ((hg.const_mul (z x+a)).intervalIntegrable _ _)
    (fun u hu => mul_le_mul_of_nonneg_right (by linarith [(hdif u hu).1] : z u ≤ z x+a) (hg0 u))
  change (∫ u in 0..P, (z x-a) * g u) ≤ ∫ u in 0..P, z u * g u at lower
  change (∫ u in 0..P, z u * g u) ≤ ∫ u in 0..P, (z x+a) * g u at upper
  rw [intervalIntegral.integral_const_mul, hm] at lower upper
  change |z x| ≤ a
  exact abs_le.mpr ⟨by nlinarith [le_of_not_gt (fun h : z x+a < 0 =>
    (not_lt_of_ge upper) (mul_neg_of_neg_of_pos h hL))],
    by nlinarith [le_of_not_gt (fun h : 0 < z x-a =>
      (not_lt_of_ge lower) (mul_pos h hL))]⟩

variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

def curvatureOscillation (S t : ℝ) := c.coreLength t *
  ∫ u in 0..c.period, (curvature (c.position t) u - S / c.coreLength t)^2 * speed (c.position t) u

theorem integrated_normalHeight_eq_zero (H : ℂ →L[ℝ] ℝ) {t : ℝ} (ht : t ∈ I) :
    (∫ u in 0..c.period, H (normal (c.position t) u) * speed (c.position t) u) = 0 := by
  let γ := c.position t
  have hg := c.position_slice_smooth ht
  have hr := c.immersion t ht
  have h (u : ℝ) : HasDerivAt (fun s => H (Complex.I * γ s))
      (H (normal γ u) * speed γ u) u := by
    apply (H.hasFDerivAt.comp_hasDerivAt u ((position_hasDerivAt hg hr u).const_mul
      Complex.I)).congr_deriv
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
    rfl
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => h u)
    (((H.continuous.comp (normal_smooth hg hr).continuous).mul
      (speed_smooth hg hr).continuous).intervalIntegrable 0 c.period)
  have hp : γ c.period = γ 0 := by simpa [γ] using c.periodic t ht 0
  rw [hp, sub_self] at hI
  exact hI

theorem height_normal_defect (H : ℂ →L[ℝ] ℝ) (hH : ‖H‖ ≤ 1) {t S x a : ℝ}
    (ht : t ∈ I) (hS : 0 < S) (ha : 0 ≤ a) (ho : c.curvatureOscillation S t ≤ a^2)
    (hx : x ∈ Icc 0 c.period) :
    |(H (c.position t x) - c.centroidHeight H t)/c.coreLength t +
      H (normal (c.position t) x)/S| ≤ a/S := by
  let γ := c.position t
  let L := c.coreLength t
  let b := c.centroidHeight H t
  let g := speed γ
  let d := fun u => curvature γ u - S/L
  let z := fun u => (H (γ u)-b)/L + H (normal γ u)/S
  let dz := fun u => -(d u / S) * H (tangent γ u) * g u
  have hL := c.coreLength_pos ht
  have hg := c.position_slice_smooth ht
  have hr := c.immersion t ht
  have hgc : Continuous g := (speed_smooth hg hr).continuous
  have hdc : Continuous d := (curvature_smooth hg hr).continuous.sub continuous_const
  have hnc : Continuous (fun u => H (normal γ u)) := H.continuous.comp (normal_smooth hg hr).continuous
  have htc : Continuous (fun u => H (tangent γ u)) := H.continuous.comp (tangent_smooth hg hr).continuous
  have hpc : Continuous (fun u => H (γ u)) := H.continuous.comp hg.continuous
  have HD (u : ℝ) : HasDerivAt z (dz u) u := by
    have h1 := (H.hasFDerivAt.comp_hasDerivAt u (position_hasDerivAt hg hr u)).sub_const b
    have h2 := H.hasFDerivAt.comp_hasDerivAt u (normal_hasDerivAt hg hr u)
    apply ((h1.div_const L).add (h2.div_const S)).congr_deriv
    rw [← Complex.ofReal_neg, ← Complex.real_smul, map_smul, map_smul]
    dsimp only [dz, d, g, smul_eq_mul]
    field_simp [hS.ne', show L ≠ 0 from hL.ne']
    ring
  have HM : (∫ u in 0..c.period, z u * g u) = 0 := by
    have heq : (fun u => z u * g u) = fun u =>
        (1/L)*(H (γ u)*g u) - (b/L)*g u + (1/S)*(H (normal γ u)*g u) := by
      funext u
      dsimp [z]
      ring
    rw [heq, intervalIntegral.integral_add (f := fun u => (1/L)*(H (γ u)*g u)-(b/L)*g u)
      (g := fun u => (1/S)*(H (normal γ u)*g u))
      (by exact ((((hpc.mul hgc).const_mul (1/L)).sub (hgc.const_mul (b/L))).intervalIntegrable _ _))
      (((hnc.mul hgc).const_mul (1/S)).intervalIntegrable _ _),
      intervalIntegral.integral_sub (f := fun u => (1/L)*(H (γ u)*g u))
      (g := fun u => (b/L)*g u) (((hpc.mul hgc).const_mul (1/L)).intervalIntegrable _ _)
      ((hgc.const_mul (b/L)).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      show (∫ u in 0..c.period, H (normal γ u)*g u) = 0 from c.integrated_normalHeight_eq_zero H ht]
    change (1/L)*c.cutoffMass H id t - (b/L)*L + (1/S)*0 = 0
    dsimp only [b, centroidHeight, L]
    field_simp [hL.ne']
    ring
  have hz := centered_oscillation HD ((((hdc.div_const S).neg.mul htc).mul hgc)) hgc
    (fun u => (speed_pos hr u).le) hL HM hx
  have hdom : (∫ u in 0..c.period, |dz u|) ≤
      ∫ u in 0..c.period, (1/S) * (|d u| * g u) := by
    apply intervalIntegral.integral_mono_on c.period_pos.le
      (((((hdc.div_const S).neg.mul htc).mul hgc).abs).intervalIntegrable _ _)
      (((hdc.abs.mul hgc).const_mul (1/S)).intervalIntegrable _ _)
    intro u _
    have hg0 : 0 ≤ g u := (speed_pos hr u).le
    have hT : |H (tangent γ u)| ≤ 1 := by
      have ht1 : ‖tangent γ u‖ = 1 := tangent_unit hr u
      simpa [Real.norm_eq_abs, ht1] using
        (H.le_opNorm (tangent γ u)).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg _))
    change |(-(d u / S) * H (tangent γ u)) * g u| ≤ (1/S) * (|d u| * g u)
    rw [abs_mul, abs_mul, abs_neg, abs_div, abs_of_pos hS, abs_of_nonneg hg0]
    calc
      _ ≤ (|d u|/S * 1) * g u := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hT (div_nonneg (abs_nonneg _) hS.le)) hg0
      _ = _ := by ring
  have hw : Continuous (fun u => Real.sqrt (g u)) := Real.continuous_sqrt.comp hgc
  have hcs := interval_integral_mul_sq_le (hdc.abs.mul hw) hw c.period_pos.le
  have eq1 : (fun u => (|d u| * Real.sqrt (g u))*Real.sqrt (g u)) = fun u => |d u| * g u := by
    funext u
    rw [mul_assoc, ← sq, Real.sq_sqrt (speed_pos hr u).le]
  have eq2 : (fun u => (|d u| * Real.sqrt (g u))^2) = fun u => d u ^ 2 * g u := by
    funext u
    rw [mul_pow, sq_abs, Real.sq_sqrt (speed_pos hr u).le]
  have eq3 : (fun u => Real.sqrt (g u)^2) = g := funext fun u => Real.sq_sqrt (speed_pos hr u).le
  change (∫ u in 0..c.period, (|d u| * Real.sqrt (g u))*Real.sqrt (g u))^2 ≤
    (∫ u in 0..c.period, (|d u| * Real.sqrt (g u))^2) * ∫ u in 0..c.period, Real.sqrt (g u)^2 at hcs
  rw [eq1, eq2, eq3] at hcs
  change L*(∫ u in 0..c.period, d u^2*g u) ≤ a^2 at ho
  change _ ≤ (∫ u in 0..c.period, d u^2*g u)*L at hcs
  have hnorm : (∫ u in 0..c.period, |d u| * g u) ≤ a := by nlinarith [hcs, ho]
  rw [intervalIntegral.integral_const_mul] at hdom
  have hscale := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 1/S from one_div_nonneg.mpr hS.le)
  rw [show (1/S)*a = a/S by ring] at hscale
  exact (hz.trans hdom).trans hscale

/-- A support direction supplied by the normal Gauss map yields an actual curve point. -/
theorem radial_support_from_normal (H : ℂ →L[ℝ] ℝ) (hH : ‖H‖ ≤ 1)
    {t S a : ℝ} (ht : t ∈ I) (hS : 0 < S) (ha : 0 ≤ a)
    (ho : c.curvatureOscillation S t ≤ a^2)
    (hit : ∃ u ∈ Icc 0 c.period, H (normal (c.position t) u) = -1) :
    ∃ u ∈ Icc 0 c.period, c.centroidHeight H t + c.coreLength t*((1-a)/S) ≤ H (c.position t u) := by
  obtain ⟨u, hu, hv⟩ := hit
  refine ⟨u, hu, ?_⟩
  have h := (abs_le.mp (c.height_normal_defect H hH ht hS ha ho hu)).1
  rw [hv] at h
  have he : (1-a)/S ≤ (H (c.position t u)-c.centroidHeight H t)/c.coreLength t := by
    rw [neg_div] at h
    linarith [show (1-a)/S = 1/S-a/S by ring]
  have hl := (le_div_iff₀ (c.coreLength_pos ht)).mp he
  linarith

#print axioms height_normal_defect
#print axioms radial_support_from_normal
end MigrationGeometry.Flow.SmoothPeriodicImmersion
