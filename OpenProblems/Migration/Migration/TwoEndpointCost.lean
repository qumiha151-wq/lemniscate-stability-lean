import Migration.ActualCutoffTransit

/-! Two cutoffs can charge separate portions of the actual spatial dissipation. -/
noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow

structure HeightCutoff where
  weight : ℝ → ℝ
  derivative : ℝ → ℝ
  localization : ℝ → ℝ
  slope : ℝ
  deriv_weight : ∀ z, HasDerivAt weight (derivative z) z
  derivative_continuous : Continuous derivative
  localization_continuous : Continuous localization
  slope_nonneg : 0 ≤ slope
  weight_nonneg : ∀ z, 0 ≤ weight z
  weight_le_one : ∀ z, weight z ≤ 1
  gradient_bound : ∀ z, |derivative z| ≤ slope*Real.sqrt (weight z)
  localization_one : ∀ z, weight z ≠ 0 → localization z=1

namespace SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem localDissipation_pair_le (H : ℂ →L[ℝ] ℝ) (a b : HeightCutoff)
    (hsep : ∀ z, a.localization z^2 + b.localization z^2 ≤ 1)
    {t : ℝ} (ht : t ∈ I) :
    c.localDissipation H a.localization t + c.localDissipation H b.localization t ≤
      c.localDissipation H (fun _ => 1) t := by
  let γ := c.position t
  let f := fun (r : ℝ → ℝ) (u : ℝ) => (r (H (γ u))*force γ u)^2*speed γ u
  have hs := c.position_slice_smooth ht
  have hreg := c.immersion t ht
  have cf (r : ℝ → ℝ) (hr : Continuous r) : Continuous (f r) :=
    ((((hr.comp H.continuous).comp hs.continuous).mul (force_smooth hs hreg).continuous).pow 2).mul
      (speed_smooth hs hreg).continuous
  change (∫ u in 0..c.period, f a.localization u) + (∫ u in 0..c.period, f b.localization u) ≤
    ∫ u in 0..c.period, f (fun _ => 1) u
  rw [← intervalIntegral.integral_add ((cf _ a.localization_continuous).intervalIntegrable _ _)
    ((cf _ b.localization_continuous).intervalIntegrable _ _)]
  apply intervalIntegral.integral_mono_on c.period_pos.le
    (((cf _ a.localization_continuous).add (cf _ b.localization_continuous)).intervalIntegrable _ _)
    ((cf _ continuous_const).intervalIntegrable _ _)
  intro u _
  have h := mul_le_mul_of_nonneg_right (hsep (H (γ u)))
    (mul_nonneg (sq_nonneg (force γ u)) (speed_pos hreg u).le)
  dsimp only [f]
  simp only [one_mul, mul_pow, Pi.add_apply]
  dsimp only [γ] at h ⊢
  linarith only [h]

/-- Consume the actual cutoff masses at the two endpoint slices. The derivative
bound and individual local dissipation costs follow from the position PDE. -/
theorem two_endpoint_transit_cost (hflow : c.IsNormalFEF) (H : ℂ →L[ℝ] ℝ) (hH : ‖H‖ ≤ 1)
    (a b : HeightCutoff) (hsep : ∀ z, a.localization z^2 + b.localization z^2 ≤ 1)
    {B U V T : ℝ} (hB : 0 < B) (hU : 0 ≤ U) (hV : 0 ≤ V) (hT : 0 < T)
    (hslab : Icc 0 T ⊆ I) (henergy : ∀ t ∈ Icc 0 T, 2*c.bending t ≤ B^2)
    (h0a : U ≤ c.cutoffMass H a.weight 0) (hTa : c.cutoffMass H a.weight T = 0)
    (h0b : c.cutoffMass H b.weight 0 = 0) (hTb : V ≤ c.cutoffMass H b.weight T) :
    (U/(B+a.slope*Real.sqrt U))^2+(V/(B+b.slope*Real.sqrt V))^2 ≤
      T * ∫ t in 0..T, c.localDissipation H (fun _ => 1) t := by
  have hca := c.actual_cutoff_transit_cost hflow H hH a.deriv_weight a.derivative_continuous
    a.localization_continuous a.slope_nonneg hB hU hT a.weight_nonneg a.weight_le_one
    a.gradient_bound a.localization_one hslab henergy (Or.inl ⟨h0a,hTa⟩)
  have hcb := c.actual_cutoff_transit_cost hflow H hH b.deriv_weight b.derivative_continuous
    b.localization_continuous b.slope_nonneg hB hV hT b.weight_nonneg b.weight_le_one
    b.gradient_bound b.localization_one hslab henergy (Or.inr ⟨h0b,hTb⟩)
  have hi (r : ℝ → ℝ) (hr : Continuous r) : IntervalIntegrable (c.localDissipation H r) volume 0 T :=
    ((c.localDissipation_continuousOn H hr).mono hslab).intervalIntegrable_of_Icc hT.le
  have h := intervalIntegral.integral_mono_on hT.le
    ((hi _ a.localization_continuous).add (hi _ b.localization_continuous)) (hi _ continuous_const)
    (fun t ht => c.localDissipation_pair_le H a b hsep (hslab ht))
  change (∫ t in 0..T, c.localDissipation H a.localization t + c.localDissipation H b.localization t) ≤ _ at h
  rw [intervalIntegral.integral_add (hi _ a.localization_continuous) (hi _ b.localization_continuous)] at h
  have hh := mul_le_mul_of_nonneg_left h hT.le
  rw [mul_add] at hh
  exact (add_le_add hca hcb).trans hh

end SmoothPeriodicImmersion
end MigrationGeometry.Flow
