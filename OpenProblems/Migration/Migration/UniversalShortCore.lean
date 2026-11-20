import Migration.MaximumAreaCenter
import Migration.DirectionalWidth
import Migration.SupportRecession

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

def recessionThreshold (η : ℝ) := η^3/(Real.pi+Real.sqrt (2*η))^2

/-- One initial-slice center works for every later time and every chosen
radius parameter satisfying the explicit energy-drop condition. -/
theorem common_disk_of_energy_drop (hf : c.IsNormalFEF) {s : ℝ} (hs : s∈I) :
    ∃ p : ℂ, ∀ {t η : ℝ}, s ≤ t → Icc s t ⊆ I → 0 < η → η < 2/3 →
      (t-s)*c.bending s^3*(c.bending s-c.bending t) < recessionThreshold η →
      Metric.closedBall p ((2/3-η)/c.bending s) ⊆ convexHull ℝ (c.position t '' Icc 0 c.period) := by
  let A := c.position s '' Icc 0 c.period
  let E := c.bending s
  have hE : 0<E := c.bending_pos_of_width hs
  have hW : 0<2/E := div_pos (by norm_num) hE
  have hA : IsCompact A := isCompact_Icc.image (c.position_slice_smooth hs).continuous
  have hw (e : ℂ) (he : ‖e‖=1) : ∃ x∈A, ∃ y∈A, 2/E ≤ inner ℝ e x-inner ℝ e y := by
    obtain ⟨lo,hi,hr,hb⟩ := c.directional_width_range hs e he
    obtain ⟨u,hu,hu'⟩ := hr.2.1
    obtain ⟨v,hv,hv'⟩ := hr.2.2
    refine ⟨c.position s v,⟨v,hv,rfl⟩,c.position s u,⟨u,hu,rfl⟩,?_⟩
    change 2/E ≤ innerSL ℝ e (c.position s v) - innerSL ℝ e (c.position s u)
    rw [hv',hu']
    exact (div_le_iff₀ hE).mpr (by linarith)
  obtain ⟨p,hp⟩ := exists_center_of_uniform_width hA hW hw
  refine ⟨p,?_⟩
  intro t η hst hslab hη hηsmall htime x hx
  apply mem_convexHull_of_surrounding_directions
  intro e he
  let H : ℂ →L[ℝ] ℝ := innerSL ℝ e
  have hH : ‖H‖ ≤ 1 := by dsimp [H]; rw [innerSL_apply_norm,he]
  obtain ⟨y,⟨u,hu,rfl⟩,hsup⟩ := hp e he
  obtain ⟨lo,hi,hr,hb⟩ := c.directional_width_range hs e he
  have hsup' : H p+(2/E)/3 ≤ hi := hsup.trans (hr.1 u hu).2
  have hx' : inner ℝ e x - H p ≤ (2/3-η)/E := by
    have h := real_inner_le_norm e (x-p)
    rw [inner_sub_right,he,one_mul] at h
    exact h.trans (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx)
  have hpq : H p + (2/3-η)/E ≤ hi-η/E := by
    linarith [show (2/3-η)/E+η/E = (2/E)/3 by ring]
  have hhit : ∃ v ∈ Icc 0 c.period, hi-η/E < H (c.position t v) := by
    rcases hst.eq_or_lt with heq|hlt
    · obtain ⟨v,hv,hv'⟩ := hr.2.2
      refine ⟨v,hv,?_⟩
      rw [← heq]
      change _ < innerSL ℝ e (c.position s v)
      rw [hv']
      linarith [div_pos hη hE]
    · by_contra! hmiss
      have hwidth : η/E ≤ hi-lo := by
        apply (div_le_iff₀ hE).mpr
        change 2 ≤ E*(hi-lo) at hb
        linarith
      have hc := c.scaled_support_recession_cost hf H hH hlt hη hwidth hslab hE hr hmiss
      exact (not_lt_of_ge hc) htime
  obtain ⟨v,hv,hv'⟩ := hhit
  refine ⟨c.position t v,⟨v,hv,rfl⟩,?_⟩
  change inner ℝ e x < H (c.position t v)
  linarith

/-- A concrete physical time valid for every smooth closed immersed
normal flow. The same center and radius work at every time in the window. -/
theorem universal_short_time_disk (hf : c.IsNormalFEF) {s : ℝ} (hs : s∈I) :
    ∃ p : ℂ, ∀ {t : ℝ}, s ≤ t → Icc s t ⊆ I →
      (t-s)*c.bending s^4 < (1/27)/(Real.pi+Real.sqrt (2/3))^2 →
      Metric.closedBall p (1/(3*c.bending s)) ⊆ convexHull ℝ (c.position t '' Icc 0 c.period) := by
  obtain ⟨p,hp⟩ := c.common_disk_of_energy_drop hf hs
  refine ⟨p,?_⟩
  intro t hst hslab htime
  have hc : (t-s)*c.bending s^3*(c.bending s-c.bending t) ≤ (t-s)*c.bending s^4 := by
    have hh := mul_nonneg (mul_nonneg (sub_nonneg.mpr hst) (pow_nonneg (c.bending_nonneg s) 3))
      (c.bending_nonneg t)
    nlinarith
  have htime' : (t-s)*c.bending s^3*(c.bending s-c.bending t) < recessionThreshold (1/3) := by
    apply hc.trans_lt
    norm_num [recessionThreshold] at htime ⊢
    exact htime
  have h := hp hst hslab (by norm_num : (0:ℝ) < 1/3) (by norm_num) htime'
  convert h using 2
  ring

#print axioms common_disk_of_energy_drop
#print axioms universal_short_time_disk
end MigrationGeometry.Flow.SmoothPeriodicImmersion
