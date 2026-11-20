import Migration.LocalizedFirstVariation

/-! Local dissipation controls the rate of change of a height-weighted length. -/
noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow

private theorem cutoffPoint_bound {k p d n F g r A : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hA : 0 ≤ A) (hd : |d| ≤ A*Real.sqrt p)
    (hn : |n| ≤ 1) (hg : 0 ≤ g) (hr : p ≠ 0 → r=1) :
    |(k*p-d*n)*F*g| ≤ |(k*Real.sqrt g)*(r*F*Real.sqrt g)| +
      A * |(Real.sqrt p * Real.sqrt g)*(r*F*Real.sqrt g)| := by
  by_cases hz : p = 0
  · subst p
    simp only [Real.sqrt_zero, mul_zero] at hd
    have hdz := abs_nonpos_iff.mp hd
    simp [hdz]
    positivity
  rw [hr hz, one_mul]
  have hkn : |k*p-d*n| ≤ |k| + A*Real.sqrt p := by
    calc
      _ ≤ |k*p| + |d*n| := abs_sub _ _
      _ = |k| * p + |d| * |n| := by simp [abs_mul, abs_of_nonneg hp]
      _ ≤ |k| * 1 + (A*Real.sqrt p)*1 :=
        add_le_add (mul_le_mul_of_nonneg_left hp1 (abs_nonneg _))
          (mul_le_mul hd hn (abs_nonneg _) (mul_nonneg hA (Real.sqrt_nonneg _)))
      _ = _ := by ring
  have hscale (a b : ℝ) : (a*Real.sqrt g)*(b*Real.sqrt g) = a*b*g := by
    calc _ = a*b*(Real.sqrt g)^2 := by ring
         _ = _ := by rw [Real.sq_sqrt hg]
  simp only [hscale, abs_mul, abs_of_nonneg hg, abs_of_nonneg (Real.sqrt_nonneg p)]
  calc
    _ ≤ (|k|+A*Real.sqrt p)*|F| * g :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkn (abs_nonneg _)) hg
    _ = _ := by ring

namespace SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

def bending (t : ℝ) : ℝ :=
  (∫ u in 0..c.period, curvature (c.position t) u^2 * speed (c.position t) u)/2

/-- A continuous localization factor equal to one on the support of the
spatial cutoff can taper within the gap between the two endpoint curves. -/
def localDissipation (H : ℂ →L[ℝ] ℝ) (r : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in 0..c.period, (r (H (c.position t u))*force (c.position t) u)^2 * speed (c.position t) u

theorem cutoffMassRate_bound (H : ℂ →L[ℝ] ℝ) (hH : ‖H‖ ≤ 1)
    (p dp r : ℝ → ℝ) (hc : Continuous p) (hdc : Continuous dp) (hrc : Continuous r)
    {A : ℝ} (hA : 0 ≤ A) (hp : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1)
    (hd : ∀ z, |dp z| ≤ A*Real.sqrt (p z)) (hr : ∀ z, p z ≠ 0 → r z = 1)
    {t : ℝ} (ht : t ∈ I) :
    |c.cutoffMassRate H p dp t| ≤ (Real.sqrt (2*c.bending t)+A*Real.sqrt (c.cutoffMass H p t))*
      Real.sqrt (c.localDissipation H r t) := by
  let γ := c.position t
  let g := speed γ
  let h := fun u => H (γ u)
  let K := fun u => curvature γ u * Real.sqrt (g u)
  let M := fun u => Real.sqrt (p (h u)) * Real.sqrt (g u)
  let F := fun u => r (h u) * force γ u * Real.sqrt (g u)
  let R := fun u => (curvature γ u*p (h u)-dp (h u)*H (normal γ u))*force γ u * g u
  have hs := c.position_slice_smooth ht
  have hreg := c.immersion t ht
  have ch : Continuous h := H.continuous.comp hs.continuous
  have cg : Continuous g := (speed_smooth hs hreg).continuous
  have ck : Continuous K := (curvature_smooth hs hreg).continuous.mul cg.sqrt
  have cm : Continuous M := ((hc.comp ch).sqrt).mul cg.sqrt
  have cf : Continuous F := ((hrc.comp ch).mul (force_smooth hs hreg).continuous).mul cg.sqrt
  have cr : Continuous R := ((((curvature_smooth hs hreg).continuous.mul (hc.comp ch)).sub
    ((hdc.comp ch).mul (H.continuous.comp (normal_smooth hs hreg).continuous))).mul
    (force_smooth hs hreg).continuous).mul cg
  have hg (u) : 0 ≤ g u := (speed_pos hreg u).le
  have hn (u) : |H (normal γ u)| ≤ 1 := by
    have hu : ‖normal γ u‖ = 1 := normal_unit hreg u
    simpa only [Real.norm_eq_abs, hu, mul_one] using (H.le_opNorm (normal γ u)).trans
      (mul_le_mul_of_nonneg_right hH (norm_nonneg _))
  have hpt : ∀ u, |R u| ≤ |K u * F u| + A * |M u * F u| := fun u =>
    cutoffPoint_bound (hp _) (hp1 _) hA (hd _) (hn _) (hg _) (hr _)
  have hIntK : (∫ u in 0..c.period, K u^2) = 2*c.bending t := by
    unfold bending
    rw [show ∀ z : ℝ, 2*(z/2)=z by intro z; ring]
    apply intervalIntegral.integral_congr
    intro u _
    simp only [K, mul_pow, Real.sq_sqrt (hg u), γ, g]
  have hIntM : (∫ u in 0..c.period, M u^2) = c.cutoffMass H p t := by
    apply intervalIntegral.integral_congr
    intro u _
    simp only [M, mul_pow, Real.sq_sqrt (hg u), Real.sq_sqrt (hp _), h, γ, g]
  have hIntF : (∫ u in 0..c.period, F u^2) = c.localDissipation H r t := by
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only [F]
    rw [mul_pow, Real.sq_sqrt (hg u)]
  have hP := c.period_pos.le
  have hk := interval_integral_abs_mul_le ck cf hP
  have hm := interval_integral_abs_mul_le cm cf hP
  rw [hIntK,hIntF] at hk
  rw [hIntM,hIntF] at hm
  change |∫ u in 0..c.period, R u| ≤ _
  calc
    _ ≤ ∫ u in 0..c.period, |R u| := intervalIntegral.abs_integral_le_integral_abs hP
    _ ≤ ∫ u in 0..c.period, |K u*F u|+A*|M u*F u| :=
      intervalIntegral.integral_mono_on hP (cr.abs.intervalIntegrable _ _)
        (((ck.mul cf).abs.add ((cm.mul cf).abs.const_mul A)).intervalIntegrable _ _) (fun u _ => hpt u)
    _ = (∫ u in 0..c.period, |K u*F u|)+A*∫ u in 0..c.period, |M u*F u| := by
      rw [intervalIntegral.integral_add (f := fun u => |K u*F u|)
        (g := fun u => A*|M u*F u|) ((ck.mul cf).abs.intervalIntegrable _ _)
        (((cm.mul cf).abs.const_mul A).intervalIntegrable _ _), intervalIntegral.integral_const_mul]
    _ ≤ _ := by
      rw [add_mul, mul_assoc]
      exact add_le_add hk (mul_le_mul_of_nonneg_left hm hA)

end SmoothPeriodicImmersion
end MigrationGeometry.Flow
