import Migration.NearRoundDrift
import Migration.NearRoundVirial

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

def signedCurvatureIntegral (t : ℝ) :=
  ∫ u in 0..c.period, curvature (c.position t) u * speed (c.position t) u

theorem oscillation_energy_identity {t S : ℝ} (ht : t ∈ I) (hm : c.signedCurvatureIntegral t = S) :
    2*c.bending t*c.coreLength t = S^2 + c.curvatureOscillation S t := by
  let k := curvature (c.position t)
  let g := speed (c.position t)
  let L := c.coreLength t
  let v := S/L
  have hL := (c.coreLength_pos ht).ne'
  have ck := (curvature_smooth (c.position_slice_smooth ht) (c.immersion t ht)).continuous
  have cg := (speed_smooth (c.position_slice_smooth ht) (c.immersion t ht)).continuous
  have heq : (fun u => (k u-v)^2*g u) = fun u =>
      k u^2*g u - (2*v)*(k u*g u) + v^2*g u := by funext u; ring
  change 2*((∫ u in 0..c.period, k u^2*g u)/2)*L = S^2+L*(∫ u in 0..c.period, (k u-v)^2*g u)
  rw [heq, intervalIntegral.integral_add (f := fun u => k u^2*g u-(2*v)*(k u*g u))
    (g := fun u => v^2*g u)
    ((((ck.pow 2).mul cg).sub ((ck.mul cg).const_mul (2*v))).intervalIntegrable _ _)
    ((cg.const_mul (v^2)).intervalIntegrable _ _), intervalIntegral.integral_sub
    (f := fun u => k u^2*g u) (g := fun u => (2*v)*(k u*g u))
    (((ck.pow 2).mul cg).intervalIntegrable _ _) (((ck.mul cg).const_mul (2*v)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    show (∫ u in 0..c.period, k u*g u) = S from hm]
  change _ = S^2+L*((∫ u in 0..c.period, k u^2*g u) - 2*v*S + v^2*L)
  dsimp only [v,L]
  field_simp
  ring

theorem curvatureOscillation_nonneg {t : ℝ} (ht : t ∈ I) (S : ℝ) : 0 ≤ c.curvatureOscillation S t :=
  mul_nonneg (c.coreLength_pos ht).le (intervalIntegral.integral_nonneg_of_forall c.period_pos.le
    (fun u => mul_nonneg (sq_nonneg _) (speed_pos (c.immersion t ht) u).le))

theorem bending_le_near_round_virial (H : ℂ →L[ℝ] ℝ) {t S a : ℝ} (ht : t ∈ I)
    (hS : 0 < S) (ha : 0 ≤ a) (ho : c.curvatureOscillation S t ≤ a^2) :
    c.bending t ≤ (1+a)*c.coreLength t/S * Real.sqrt (c.coreLength t) *
      Real.sqrt (c.localDissipation H (fun _ => 1) t) := by
  let γ := c.position t
  let g := speed γ
  let f := force γ
  let p := c.arclengthCentroid t
  let h := fun u => inner ℝ (normal γ u) (γ u-p)
  let m := (1+a)*c.coreLength t/S
  let D := c.localDissipation H (fun _ => 1) t
  have hg := c.position_slice_smooth ht
  have hr := c.immersion t ht
  have cg := (speed_smooth hg hr).continuous
  have cf := (force_smooth hg hr).continuous
  have ch : Continuous h := (normal_smooth hg hr).continuous.inner (hg.continuous.sub continuous_const)
  have gp (u) : 0 ≤ g u := (speed_pos hr u).le
  have hm : 0 ≤ m := div_nonneg (mul_nonneg (by linarith) (c.coreLength_pos ht).le) hS.le
  have hb (u : ℝ) (hu : u ∈ Icc 0 c.period) : |h u| ≤ m := by
    have hs := c.signed_normal_support_bounds ht hS ha ho hu
    change -(1+a)*c.coreLength t/S ≤ h u ∧ h u ≤ -(1-a)*c.coreLength t/S at hs
    apply abs_le.mpr
    constructor
    · simpa only [m,neg_mul,neg_div] using hs.1
    · apply hs.2.trans
      apply div_le_div_of_nonneg_right _ hS.le
      exact mul_le_mul_of_nonneg_right (by linarith : -(1-a) ≤ 1+a) (c.coreLength_pos ht).le
  have hw := weighted_abs_force (v := fun _ => 1) c.period_pos.le continuous_const cf cg gp
  have hD : (∫ u in 0..c.period, f u^2*g u) = D := by simp [D,localDissipation,g,f,γ]
  simp only [abs_one,one_mul,one_pow] at hw
  change _ ≤ _ * Real.sqrt (∫ u in 0..c.period, f u^2*g u) at hw
  rw [hD] at hw
  change (∫ u in 0..c.period, |f u| * g u) ≤ Real.sqrt (c.coreLength t) * Real.sqrt D at hw
  have hv := c.material_virial ht p
  change (∫ u in 0..c.period, g u*f u*h u) = -c.bending t at hv
  have hE : c.bending t = |∫ u in 0..c.period, g u*f u*h u| := by
    rw [hv, abs_neg, abs_of_nonneg (c.bending_nonneg t)]
  rw [hE]
  apply (intervalIntegral.abs_integral_le_integral_abs c.period_pos.le).trans
  calc
    _ ≤ ∫ u in 0..c.period, m*(|f u| * g u) := by
      apply intervalIntegral.integral_mono_on c.period_pos.le
        (((cg.mul cf).mul ch).abs.intervalIntegrable _ _)
        (((cf.abs.mul cg).const_mul m).intervalIntegrable _ _)
      intro u hu
      change |g u*f u*h u| ≤ m*(|f u| * g u)
      rw [abs_mul, abs_mul, abs_of_nonneg (gp u)]
      nlinarith [mul_le_mul_of_nonneg_left (hb u hu) (mul_nonneg (gp u) (abs_nonneg (f u)))]
    _ ≤ _ := by
      rw [intervalIntegral.integral_const_mul]
      simpa only [mul_assoc,m,D] using mul_le_mul_of_nonneg_left hw hm

#print axioms oscillation_energy_identity
#print axioms bending_le_near_round_virial
end MigrationGeometry.Flow.SmoothPeriodicImmersion
