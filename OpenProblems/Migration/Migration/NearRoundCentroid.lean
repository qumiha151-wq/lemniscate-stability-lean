import Migration.BendingDissipation
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion

variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

def coreLength (t : ℝ) := ∫ u in 0..c.period, speed (c.position t) u

def centroidHeight (H : ℂ →L[ℝ] ℝ) (t : ℝ) :=
  c.cutoffMass H id t / c.coreLength t

def centroidRate (H : ℂ →L[ℝ] ℝ) (t : ℝ) :=
  (∫ u in 0..c.period, (curvature (c.position t) u *
    (H (c.position t u) - c.centroidHeight H t) + H (normal (c.position t) u)) *
    force (c.position t) u * speed (c.position t) u) / c.coreLength t

theorem coreLength_pos {t : ℝ} (ht : t ∈ I) : 0 < c.coreLength t := by
  apply intervalIntegral.integral_pos c.period_pos
    (speed_smooth (c.position_slice_smooth ht) (c.immersion t ht)).continuous.continuousOn
  · exact fun u _ => (speed_pos (c.immersion t ht) u).le
  · exact ⟨0, ⟨le_rfl, c.period_pos.le⟩, speed_pos (c.immersion t ht) 0⟩

theorem integrated_normalForce_eq_zero (H : ℂ →L[ℝ] ℝ) {t : ℝ} (ht : t ∈ I) :
    (∫ u in 0..c.period, H (normal (c.position t) u) * force (c.position t) u *
      speed (c.position t) u) = 0 := by
  let γ := c.position t
  have hg := c.position_slice_smooth ht
  have hr := c.immersion t ht
  have h (u : ℝ) : HasDerivAt (fun s => H (stress γ s))
      (H (normal γ u) * force γ u * speed γ u) u := by
    apply (H.hasFDerivAt.comp_hasDerivAt u (stress_hasDerivAt hg hr u)).congr_deriv
    rw [← Complex.real_smul, map_smul, smul_eq_mul]
    ring
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => h u)
    ((((H.continuous.comp (normal_smooth hg hr).continuous).mul
      (force_smooth hg hr).continuous).mul (speed_smooth hg hr).continuous).intervalIntegrable 0 c.period)
  have hp : stress γ c.period = stress γ 0 := by simpa [γ] using stress_periodic hg hr (c.periodic t ht) 0
  rw [hp, sub_self] at hI
  exact hI

theorem centroidHeight_hasDerivAt (hf : c.IsNormalFEF) (H : ℂ →L[ℝ] ℝ)
    {t : ℝ} (ht : t ∈ I) : HasDerivAt (c.centroidHeight H) (c.centroidRate H t) t := by
  let γ := c.position t
  let b := c.centroidHeight H t
  let A := fun u => (curvature γ u * H (γ u) - H (normal γ u)) * force γ u * speed γ u
  let K := fun u => curvature γ u * force γ u * speed γ u
  let N := fun u => H (normal γ u) * force γ u * speed γ u
  have hg := c.position_slice_smooth ht
  have hr := c.immersion t ht
  have hK : Continuous K := ((curvature_smooth hg hr).continuous.mul
    (force_smooth hg hr).continuous).mul (speed_smooth hg hr).continuous
  have hN : Continuous N := ((H.continuous.comp (normal_smooth hg hr).continuous).mul
    (force_smooth hg hr).continuous).mul (speed_smooth hg hr).continuous
  have hA : Continuous A := ((((curvature_smooth hg hr).continuous.mul (H.continuous.comp
    hg.continuous)).sub (H.continuous.comp (normal_smooth hg hr).continuous)).mul
      (force_smooth hg hr).continuous).mul (speed_smooth hg hr).continuous
  have hlen (v : ℝ) : c.cutoffMass H (fun _ => 1) v = c.coreLength v := by
    simp [cutoffMass, coreLength]
  have hdL := c.cutoffMass_hasDerivAt hf H (fun _ => 1) (fun _ => 0)
    (fun u => hasDerivAt_const u (1 : ℝ)) continuous_const ht
  rw [funext hlen] at hdL
  have hdl : HasDerivAt c.coreLength (∫ u in 0..c.period, K u) t := by
    simpa [cutoffMassRate, K, γ] using hdL
  have hdm : HasDerivAt (c.cutoffMass H id) (∫ u in 0..c.period, A u) t := by
    simpa [cutoffMassRate, A, γ] using c.cutoffMass_hasDerivAt hf H id (fun _ => 1)
      hasDerivAt_id continuous_const ht
  have hL := (c.coreLength_pos ht).ne'
  apply (hdm.div hdl hL).congr_deriv
  have hform : (fun u => (curvature γ u * (H (γ u) - b) + H (normal γ u)) *
      force γ u * speed γ u) = (fun u => (A u - b * K u) + 2 * N u) := by
    funext u
    dsimp [A,K,N]
    ring
  change _ = (∫ u in 0..c.period, (curvature γ u * (H (γ u) - b) + H (normal γ u)) *
      force γ u * speed γ u) / c.coreLength t
  rw [hform, intervalIntegral.integral_add (f := fun u => A u - b*K u)
    ((hA.sub (hK.const_mul b)).intervalIntegrable _ _)
    ((hN.const_mul 2).intervalIntegrable _ _), intervalIntegral.integral_sub
    (hA.intervalIntegrable _ _) ((hK.const_mul b).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    show (∫ u in 0..c.period, N u) = 0 from c.integrated_normalForce_eq_zero H ht]
  dsimp only [b, centroidHeight]
  field_simp
  ring

private theorem change_le_of_rate {s t : ℝ} (hst : s ≤ t)
    {f p df dp : ℝ → ℝ}
    (hf : ∀ x ∈ Icc s t, HasDerivAt f (df x) x)
    (hp : ∀ x ∈ Icc s t, HasDerivAt p (dp x) x)
    (hbound : ∀ x ∈ Icc s t, df x ≤ dp x) : f t - f s ≤ p t - p s := by
  have hd := fun x (hx : x ∈ Icc s t) => (hf x hx).sub (hp x hx)
  have ha : AntitoneOn (fun x => f x - p x) (Icc s t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc s t)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      change deriv (f-p) x ≤ 0
      rw [(hd x (interior_subset hx)).deriv]
      exact sub_nonpos.mpr (hbound x (interior_subset hx))
  have he := ha (show s ∈ Icc s t from ⟨le_rfl,hst⟩) (show t ∈ Icc s t from ⟨hst,le_rfl⟩) hst
  dsimp at he
  linarith

/-- Integrate a force-rate bound using the energy drop of the actual position-defined flow. -/
theorem centroid_displacement_of_force_bound (hf : c.IsNormalFEF) (H : ℂ →L[ℝ] ℝ)
    {s t C : ℝ} (hst : s ≤ t) (hslab : Icc s t ⊆ I)
    (hE : ∀ v ∈ Icc s t, 0 < c.bending v)
    (hrate : ∀ v ∈ Icc s t, |c.centroidRate H v| ≤
      C * c.localDissipation H (fun _ => 1) v / c.bending v ^ 2) :
    |c.centroidHeight H t - c.centroidHeight H s| ≤ C / c.bending t - C / c.bending s := by
  let d := fun v => C * c.localDissipation H (fun _ => 1) v / c.bending v ^ 2
  have hp (v : ℝ) (hv : v ∈ Icc s t) :
      HasDerivAt (fun x => C / c.bending x) (d v) v := by
    apply ((hasDerivAt_const v C).div (c.bending_hasDerivAt_dissipation hf H (hslab hv))
      (hE v hv).ne').congr_deriv
    dsimp [d]
    ring
  have hpos := change_le_of_rate hst (fun v hv => c.centroidHeight_hasDerivAt hf H (hslab hv))
    hp (fun v hv => (abs_le.mp (hrate v hv)).2)
  have hneg := change_le_of_rate hst (fun v hv => (c.centroidHeight_hasDerivAt hf H (hslab hv)).neg)
    hp (fun v hv => neg_le.mp (abs_le.mp (hrate v hv)).1)
  exact abs_le.mpr ⟨by dsimp at hneg; linarith, hpos⟩

#print axioms centroidHeight_hasDerivAt
#print axioms centroid_displacement_of_force_bound

end MigrationGeometry.Flow.SmoothPeriodicImmersion
