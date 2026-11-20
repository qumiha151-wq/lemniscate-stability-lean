import Migration.NearRoundSupport

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion

theorem weighted_abs_force {v f g : ℝ → ℝ} {P : ℝ}
    (hP : 0 ≤ P) (hv : Continuous v) (hf : Continuous f) (hg : Continuous g)
    (hp : ∀ u, 0 ≤ g u) :
    (∫ u in 0..P, |v u| * |f u| * g u) ≤
      Real.sqrt (∫ u in 0..P, v u^2*g u) * Real.sqrt (∫ u in 0..P, f u^2*g u) := by
  let V := fun u => v u * Real.sqrt (g u)
  let F := fun u => f u * Real.sqrt (g u)
  have hcs := interval_integral_abs_mul_le (hv.mul hg.sqrt) (hf.mul hg.sqrt) hP
  change (∫ u in 0..P, |V u*F u|) ≤ Real.sqrt (∫ u in 0..P, V u^2) *
    Real.sqrt (∫ u in 0..P, F u^2) at hcs
  have e1 : (fun u => |V u * F u|) = fun u => |v u| * |f u| * g u := by
    funext u
    rw [show V u*F u = (v u*f u)*(Real.sqrt (g u))^2 by dsimp [V,F]; ring,
      Real.sq_sqrt (hp u), abs_mul, abs_mul, abs_of_nonneg (hp u)]
  have e2 (w : ℝ → ℝ) : (fun u => (w u*Real.sqrt (g u))^2) = fun u => w u^2*g u := by
    funext u
    rw [mul_pow, Real.sq_sqrt (hp u)]
  simpa only [e1, V, F, e2] using hcs

variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- The curvature oscillation of the actual immersion bounds the projected
centroid rate without an assumed bound on any of its spatial derivatives. -/
theorem centroidRate_near_round (H : ℂ →L[ℝ] ℝ) (hH : ‖H‖ ≤ 1)
    {t S a : ℝ} (ht : t ∈ I) (hS : 0 < S) (ha : 0 ≤ a)
    (ho : c.curvatureOscillation S t ≤ a^2) :
    |c.centroidRate H t| * c.coreLength t ≤
      a*(1+(1+a)/S)*Real.sqrt (c.coreLength t)*
      Real.sqrt (c.localDissipation H (fun _ => 1) t) := by
  let γ := c.position t
  let g := speed γ
  let L := c.coreLength t
  let F := force γ
  let Y := fun u => H (γ u) - c.centroidHeight H t
  let N := fun u => H (normal γ u)
  let d := fun u => curvature γ u - S/L
  let Q := fun u => curvature γ u*Y u+N u
  let m := L*(1+a)/S
  let A := ∫ u in 0..c.period, d u^2 * g u
  let D := c.localDissipation H (fun _ => 1) t
  have hL : 0 < L := c.coreLength_pos ht
  have hg := c.position_slice_smooth ht
  have hr := c.immersion t ht
  have cg : Continuous g := (speed_smooth hg hr).continuous
  have cf : Continuous F := (force_smooth hg hr).continuous
  have cy : Continuous Y := (H.continuous.comp hg.continuous).sub continuous_const
  have cn : Continuous N := H.continuous.comp (normal_smooth hg hr).continuous
  have cd : Continuous d := (curvature_smooth hg hr).continuous.sub continuous_const
  have cq : Continuous Q := ((curvature_smooth hg hr).continuous.mul cy).add cn
  have gp (u) : 0 ≤ g u := (speed_pos hr u).le
  have hd (u : ℝ) (hu : u ∈ Icc 0 c.period) : |(S/L)*Y u+N u| ≤ a := by
    have h := c.height_normal_defect H hH ht hS ha ho hu
    change |Y u/L + N u/S| ≤ a/S at h
    have hh := mul_le_mul_of_nonneg_left h hS.le
    rw [← abs_of_pos hS, ← abs_mul] at hh
    have e : S*(Y u/L+N u/S) = S/L*Y u+N u := by field_simp
    simpa [e, abs_of_pos hS, mul_div_cancel₀ a hS.ne', mul_comm S (a/S)] using hh
  have hq (u : ℝ) (hu : u ∈ Icc 0 c.period) : |Q u| ≤ m * |d u| + a := by
    have hn : |N u| ≤ 1 := by
      have h₁ : ‖normal γ u‖ = 1 := normal_unit hr u
      simpa only [N, Real.norm_eq_abs, h₁, mul_one] using (H.le_opNorm (normal γ u)).trans
        (mul_le_mul_of_nonneg_right hH (norm_nonneg _))
    have hsum : |S/L*Y u| ≤ a+1 := by
      calc
        _ = |(S/L*Y u+N u)-N u| := by ring_nf
        _ ≤ |S/L*Y u+N u|+|N u| := abs_sub _ _
        _ ≤ _ := add_le_add (hd u hu) hn
    rw [abs_mul, abs_of_pos (div_pos hS hL)] at hsum
    have hy : |Y u| ≤ m := by
      apply (le_div_iff₀ hS).mpr
      have hh := mul_le_mul_of_nonneg_left hsum hL.le
      have e : L*(S/L*|Y u|) = |Y u| * S := by field_simp
      rw [e] at hh
      linarith
    have he : Q u = d u*Y u + (S/L*Y u+N u) := by dsimp [Q,d]; ring
    rw [he]
    have hp : |d u * Y u| ≤ m * |d u| := by
      rw [abs_mul, mul_comm m]
      exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
    exact (abs_add_le _ _).trans (add_le_add hp (hd u hu))
  have hA : 0 ≤ A := intervalIntegral.integral_nonneg_of_forall c.period_pos.le
    (fun u => mul_nonneg (sq_nonneg (d u)) (gp u))
  have hAmp : L * Real.sqrt A ≤ a * Real.sqrt L := by
    change L*A ≤ a^2 at ho
    have hh := mul_le_mul_of_nonneg_left ho hL.le
    have e1 : (L*Real.sqrt A)^2 = L^2*A := by rw [mul_pow, Real.sq_sqrt hA]
    have e2 : (a*Real.sqrt L)^2 = a^2*L := by rw [mul_pow, Real.sq_sqrt hL.le]
    nlinarith [mul_nonneg ha (Real.sqrt_nonneg L)]
  have hD : (∫ u in 0..c.period, F u^2*g u) = D := by simp [D,localDissipation,g,F,γ]
  have h1 := weighted_abs_force c.period_pos.le cd cf cg gp
  rw [hD] at h1
  have h2 := weighted_abs_force (v := fun _ => 1) c.period_pos.le continuous_const cf cg gp
  simp only [one_pow, one_mul, abs_one, hD] at h2
  change (∫ u in 0..c.period, |F u| * g u) ≤ Real.sqrt L * Real.sqrt D at h2
  let U := fun u => |d u| * |F u| * g u
  let V := fun u => |F u| * g u
  have cu : Continuous U := (cd.abs.mul cf.abs).mul cg
  have cv : Continuous V := cf.abs.mul cg
  have hm : 0 ≤ m := div_nonneg (mul_nonneg hL.le (by linarith)) hS.le
  have hb : |∫ u in 0..c.period, Q u*F u*g u| ≤
      m*(Real.sqrt A*Real.sqrt D) + a*(Real.sqrt L*Real.sqrt D) := by
    apply (intervalIntegral.abs_integral_le_integral_abs c.period_pos.le).trans
    calc
      _ ≤ ∫ u in 0..c.period, m*U u + a*V u := by
        apply intervalIntegral.integral_mono_on c.period_pos.le
          (((cq.mul cf).mul cg).abs.intervalIntegrable _ _)
          (((cu.const_mul m).add (cv.const_mul a)).intervalIntegrable _ _)
        intro u hu
        change |Q u*F u*g u| ≤ m*U u + a*V u
        rw [abs_mul, abs_mul, abs_of_nonneg (gp u)]
        calc
          _ ≤ (m * |d u| + a) * |F u| * g u := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hq u hu) (abs_nonneg _)) (gp u)
          _ = _ := by dsimp [U,V]; ring
      _ = m*(∫ u in 0..c.period, U u) + a*(∫ u in 0..c.period, V u) := by
        rw [intervalIntegral.integral_add ((cu.const_mul m).intervalIntegrable _ _)
          ((cv.const_mul a).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h1 hm) (mul_le_mul_of_nonneg_left h2 ha)
  have hmA : m*Real.sqrt A ≤ ((1+a)/S)*(a*Real.sqrt L) := by
    have hh := mul_le_mul_of_nonneg_left hAmp (div_nonneg (by linarith : 0≤1+a) hS.le)
    calc
      _ = ((1+a)/S)*(L*Real.sqrt A) := by dsimp [m]; ring
      _ ≤ _ := hh
  change |(∫ u in 0..c.period, Q u*F u*g u)/L| * L ≤ _
  rw [abs_div, abs_of_pos hL, div_mul_cancel₀ _ hL.ne']
  apply hb.trans
  change _ ≤ a*(1+(1+a)/S)*Real.sqrt L*Real.sqrt D
  nlinarith [mul_le_mul_of_nonneg_right hmA (Real.sqrt_nonneg D)]

#print axioms centroidRate_near_round
end MigrationGeometry.Flow.SmoothPeriodicImmersion
