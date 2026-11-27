import LengthGrowth.ActualFlow.CurvatureMomentCone

noncomputable section
open MeasureTheory Set
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- Normalizing by a signed RMS curvature simultaneously treats either
orientation. The dispersion of the actual normal force gives the last bound. -/
theorem physical_curvature_moment_pencil (hf : c.IsNormalFEF) {t r : ℝ} (ht : 0<t)
    (hr : r≠0) (scale : c.length t*r^2=2*c.energy t)
    (record : 0 ≤ deriv c.normalizedProduct t) :
    let L := c.length t
    let μ := materialSignedCurvature (c.position t) c.period/(L*r)
    let H := materialCubicCurvature (c.position t) c.period/(L*r^3)
    (∀ d : ℝ, (∀ u, -d≤curvature (c.position t) u/r) →
      (0≤μ+d ∧ ∀ x : ℝ, 0≤(μ+d)*(x*x)-2*(1+d*μ)*x+H+d)) ∧
    (2*H-μ)^2 ≤ 1 := by
  let γ := c.position t
  let L := c.length t
  let μ := materialSignedCurvature γ c.period/(L*r)
  let H := materialCubicCurvature γ c.period/(L*r^3)
  let k := fun u => curvature γ u/r
  let w := speed γ
  have lp : 0<L := c.length_pos ht.le
  have hs := c.position_slice_smooth ht.le
  have reg := c.immersion t ht.le
  have hk : Continuous k := (curvature_smooth hs reg).continuous.div_const r
  have hw : Continuous w := (speed_smooth hs reg).continuous
  have wn (u : ℝ) : 0≤w u := (speed_pos reg u).le
  have mom (j : ℕ) : (∫ u in 0..c.period, k u^j*w u) =
      (r^j)⁻¹*(∫ u in 0..c.period, curvature γ u^j*w u) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only [k]
    rw [div_pow,div_eq_mul_inv]
    ring
  have mass : (∫ u in 0..c.period,w u)=L := rfl
  have one : (∫ u in 0..c.period,k u*w u)=L*μ := by
    have h := mom 1
    simp only [pow_one] at h
    rw [h]
    change r⁻¹*materialSignedCurvature γ c.period=L*μ
    dsimp only [μ]
    field_simp [lp.ne',hr]
  have two : (∫ u in 0..c.period,k u^2*w u)=L := by
    rw [mom 2]
    have h : (∫ u in 0..c.period,curvature γ u^2*w u)=2*c.energy t := by
      change (∫ u in 0..c.period,curvature γ u^2*w u) = 2*((1/2:ℝ)*(∫ u in 0..c.period,curvature γ u^2*w u))
      ring
    rw [h,←scale]
    change (r^2)⁻¹*(L*r^2)=L
    field_simp [hr]
  have three : (∫ u in 0..c.period,k u^3*w u)=L*H := by
    rw [mom 3]
    change (r^3)⁻¹*materialCubicCurvature γ c.period=L*H
    dsimp only [H]
    field_simp [lp.ne',hr]
  change (_ ∧ (2*H-μ)^2≤1)
  constructor
  · intro d hd
    have low (u : ℝ) : 0≤k u+d := by change 0≤curvature γ u/r+d; linarith [hd u]
    have nn := intervalIntegral.integral_nonneg_of_forall (μ:=volume) c.period_pos.le
      (fun u => mul_nonneg (low u) (wn u))
    have e : (∫ u in 0..c.period,(k u+d)*w u)=L*(μ+d) := by
      calc
        _ = ∫ u in 0..c.period,k u*w u+d*w u := by
          apply intervalIntegral.integral_congr
          intro u _
          dsimp only
          ring
        _ = _ := by
          rw [intervalIntegral.integral_add (f:=fun u=>k u*w u) (g:=fun u=>d*w u)
            ((hk.mul hw).intervalIntegrable ..) ((hw.const_mul d).intervalIntegrable ..),
            intervalIntegral.integral_const_mul,one,mass]
          ring
    rw [e] at nn
    exact ⟨nonneg_of_mul_nonneg_right nn lp,
      curvature_support_quadratic c.period_pos.le lp hk hw wn hd mass one two three⟩
  · have h := c.centered_cubic_deficit ht.le
    dsimp only at h
    rw [← c.signedCurvature_eq_initial ht.le,←scale] at h
    rw [(c.normalizedProduct_hasDerivAt_normal hf ht).deriv] at record
    have diff : c.length t*c.dissipation t-c.energy t*c.lengthRate t≤0 := by linarith
    have hraw : (2*L*materialCubicCurvature γ c.period-L*r^2*materialSignedCurvature γ c.period)^2
        ≤ L*(L*r^2)^3 := by
      have hn := mul_nonpos_of_nonneg_of_nonpos (show 0≤16*(c.length t)^2 by positivity) diff
      exact h.trans (add_le_of_nonpos_left hn)
    have eq : (2*H-μ)^2*(L^4*r^6)=
        (2*L*materialCubicCurvature γ c.period-L*r^2*materialSignedCurvature γ c.period)^2 := by
      dsimp only [H,μ]
      field_simp [lp.ne',hr]
    have pos : 0<L^4*r^6 := mul_pos (pow_pos lp _) (by positivity)
    apply le_of_mul_le_mul_right (a := L^4*r^6) _ pos
    rw [eq,one_mul]
    linarith only [show L*(L*r^2)^3=L^4*r^6 by ring,hraw]

/-- A necessary sharp moment inequality for both curvature extrema, at every
genuine slice where the normalized energy is not decreasing. -/
theorem actual_signed_excursion_constraint (hf : c.IsNormalFEF) {t r d : ℝ} (ht : 0<t)
    (hr : r≠0) (scale : c.length t*r^2=2*c.energy t)
    (record : 0≤deriv c.normalizedProduct t)
    (hb : ∀ u, -d≤curvature (c.position t) u/r)
    (mean : materialSignedCurvature (c.position t) c.period/(c.length t*r)<1) :
    let μ := materialSignedCurvature (c.position t) c.period/(c.length t*r)
    2+μ≤2*(1+μ)*d^2+d := by
  obtain ⟨base,force⟩ := c.physical_curvature_moment_pencil hf ht hr scale record
  obtain ⟨low,quad⟩ := base d hb
  apply signed_excursion_constraint mean low _ quad
  nlinarith only [force, sq_nonneg (2*(materialCubicCurvature (c.position t) c.period/
    (c.length t*r^3))-materialSignedCurvature (c.position t) c.period/(c.length t*r)-1)]

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.actual_signed_excursion_constraint
