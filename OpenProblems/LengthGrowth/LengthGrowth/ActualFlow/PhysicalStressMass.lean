import LengthGrowth.ActualFlow.PointStress
import LengthGrowth.ActualFlow.PhysicalSaturationGap

noncomputable section
open MeasureTheory Set

namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

/-- Positive regularization of the magnitude of the physical elastic stress. -/
def regularizedStress (a s : ℝ) : ℝ := Real.sqrt (a^4 + ‖c.stress s‖^2)

theorem regularizedStress_continuous (a : ℝ) : Continuous (c.regularizedStress a) :=
  (continuous_const.add (c.stress_continuous.norm.pow 2)).sqrt

theorem regularizedStress_pos {a : ℝ} (ha : 0 < a) (s : ℝ) :
    0 < c.regularizedStress a s := by
  unfold regularizedStress
  positivity

theorem regularizedStress_sq (a s : ℝ) :
    c.regularizedStress a s ^ 2 = a^4 + c.curvature₁ s ^ 2 + c.curvature s ^ 4 / 4 := by
  unfold regularizedStress
  rw [Real.sq_sqrt (by positivity),c.stress_norm_sq]
  ring

theorem regularizedStress_deriv {a : ℝ} (ha : 0 < a) (s : ℝ) :
    HasDerivAt (c.regularizedStress a)
      (c.curvature₁ s * c.force s / c.regularizedStress a s) s := by
  have h := ((c.stress_norm_sq_deriv s).const_add (a^4)).sqrt
    (show a^4 + ‖c.stress s‖^2 ≠ 0 by positivity)
  apply h.congr_deriv
  dsimp [regularizedStress]
  ring

private theorem regularizedStress_majorization {a k p f v : ℝ} (ha : 0<a)
    (hv : 0<v) (h : v^2=a^4+p^2+k^4/4) :
    a^4/v + 3*k^4/(4*v) - (k/v)*(1-p^2/v^2)*f ≤
      a^2 + 3/2*k^2 + |f|/a := by
  have av : a^2 ≤ v := by
    apply le_of_sq_le_sq _ hv.le
    nlinarith only [h,sq_nonneg p,sq_nonneg (k^2)]
  have kv : k^2 ≤ 2*v := by
    apply le_of_sq_le_sq _ (by positivity)
    nlinarith only [h,sq_nonneg (a^2),sq_nonneg p]
  have ak : |k| * a ≤ v := by
    apply le_of_sq_le_sq _ hv.le
    rw [mul_pow,sq_abs]
    nlinarith only [h,sq_nonneg (a^2-k^2/2),sq_nonneg p]
  have bounda : a^4/v ≤ a^2 := by
    apply (div_le_iff₀ hv).mpr
    nlinarith only [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr av)]
  have boundk : 3*k^4/(4*v) ≤ 3/2*k^2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [mul_nonneg (sq_nonneg k) (sub_nonneg.mpr kv)]
  have pv : 0 ≤ 1-p^2/v^2 := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (sq_pos_of_pos hv)).mpr
    nlinarith only [h,sq_nonneg (a^2),sq_nonneg (k^2)]
  have pv1 : 1-p^2/v^2 ≤ 1 := sub_le_self _ (by positivity)
  have kc : |k/v| ≤ 1/a := by
    rw [abs_div,abs_of_pos hv,div_le_div_iff₀ hv ha]
    linarith only [ak]
  have corr : |(k/v)*(1-p^2/v^2)*f| ≤ |f|/a := by
    rw [abs_mul,abs_mul,abs_of_nonneg pv]
    calc
      _ ≤ (1/a)*1*|f| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg f)
        exact mul_le_mul kc pv1 pv (by positivity)
      _ = _ := by ring
  linarith only [bounda,boundk,corr,neg_le_abs ((k/v)*(1-p^2/v^2)*f)]

/-- Whole-curve stress mass. The coefficient of the absolute force scales
inversely with the chosen positive regularizing curvature. -/
theorem regularizedStress_integral_le {a : ℝ} (ha : 0<a) :
    (∫s in 0..c.period, c.regularizedStress a s) ≤
      a^2*c.period + 3*c.energy + (∫s in 0..c.period, |c.force s|)/a := by
  let v := c.regularizedStress a
  let q := fun s => a^4/v s + 3*c.curvature s^4/(4*v s) -
    (c.curvature s/v s)*(1-c.curvature₁ s^2/v s^2)*c.force s
  have cv : Continuous v := c.regularizedStress_continuous _
  have vp (s) : 0<v s := c.regularizedStress_pos ha s
  have ck := c.curvature_continuous
  have cp := c.curvature₁_continuous
  have cq : Continuous q := by
    apply Continuous.sub
    · exact (continuous_const.div cv (fun s => (vp s).ne')).add
        ((continuous_const.mul (ck.pow 4)).div (continuous_const.mul cv)
          (fun s => mul_ne_zero (by norm_num) (vp s).ne'))
    · exact ((ck.div cv (fun s => (vp s).ne')).mul (continuous_const.sub
        ((cp.pow 2).div (cv.pow 2) (fun s => (pow_ne_zero 2 (vp s).ne'))))).mul c.force_continuous
  have d (s) : HasDerivAt (fun z => c.curvature z*c.curvature₁ z/v z) (v s-q s) s := by
    apply (((c.curvature_deriv s).mul (c.curvature₁_deriv s)).div
       (c.regularizedStress_deriv ha s) (vp s).ne').congr_deriv
    have h := c.regularizedStress_sq a s
    change v s ^ 2 = _ at h
    change ((c.curvature₁ s*c.curvature₁ s+c.curvature s*c.curvature₂ s)*v s -
      (c.curvature s*c.curvature₁ s)*(c.curvature₁ s*c.force s/v s))/v s^2 = _
    calc
      _ = (a^4+c.curvature₁ s^2+c.curvature s^4/4)/v s-q s := by
        dsimp only [q,force]
        field_simp [(vp s).ne']
        ring
      _ = _ := by rw [←h]; field_simp [(vp s).ne']
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=c.period)
    (fun u _ => d u) ((cv.sub cq).intervalIntegrable _ _)
  have kp : c.curvature c.period=c.curvature 0 := by simpa using c.curvature_periodic 0
  have pp : c.curvature₁ c.period=c.curvature₁ 0 := by simpa using c.curvature₁_periodic 0
  have vv : v c.period=v 0 := by
    dsimp [v,regularizedStress]
    rw [show c.stress c.period=c.stress 0 by simpa using c.stress_periodic 0]
  rw [kp,pp,vv,sub_self,intervalIntegral.integral_sub (cv.intervalIntegrable _ _)
    (cq.intervalIntegrable _ _)] at key
  change (∫s in 0..c.period,v s) ≤ _
  rw [sub_eq_zero.mp key]
  have hconst : Continuous (fun _ : ℝ => a^2) := continuous_const
  have ci := ((hconst.add ((ck.pow 2).const_mul (3/2:ℝ))).add
    (c.force_continuous.abs.div_const a)).intervalIntegrable (μ:=volume) (0:ℝ) c.period
  calc
    _ ≤ ∫s in 0..c.period, a^2+3/2*c.curvature s^2+|c.force s|/a :=
      intervalIntegral.integral_mono_on c.period_pos.le (cq.intervalIntegrable _ _) ci
        (fun s _ => regularizedStress_majorization ha (vp s) (c.regularizedStress_sq a s))
    _ = _ := by
      rw [intervalIntegral.integral_add (f:=fun s => a^2+3/2*c.curvature s^2)
        (g:=fun s => |c.force s|/a)
        ((continuous_const.add ((ck.pow 2).const_mul (3/2:ℝ))).intervalIntegrable _ _)
        ((c.force_continuous.abs.div_const a).intervalIntegrable _ _),
        intervalIntegral.integral_add (f:=fun _ => a^2) (g:=fun s => 3/2*c.curvature s^2)
          (hconst.intervalIntegrable _ _) ((ck.pow 2).const_mul (3/2:ℝ) |>.intervalIntegrable _ _),
        intervalIntegral.integral_const,intervalIntegral.integral_const_mul,intervalIntegral.integral_div]
      unfold energy
      simp only [sub_zero,smul_eq_mul]
      ring

/-- Integral of the norm of the physical stress over one arclength period. -/
def stressMass : ℝ := ∫s in 0..c.period, ‖c.stress s‖

theorem stressMass_le_regularized (a : ℝ) :
    c.stressMass ≤ ∫s in 0..c.period, c.regularizedStress a s := by
  apply intervalIntegral.integral_mono_on c.period_pos.le
    (c.stress_continuous.norm.intervalIntegrable _ _) ((c.regularizedStress_continuous _).intervalIntegrable _ _)
  intro s _
  unfold regularizedStress
  apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (by positivity)]
  exact le_add_of_nonneg_left (by positivity)

/-- Optimizing the regularization at the scale of the excess stress mass. -/
theorem stressMass_excess_cube_force :
    4*(max 0 (c.stressMass-3*c.energy))^3 ≤
      27*c.period*(∫s in 0..c.period, |c.force s|)^2 := by
  let x := c.stressMass-3*c.energy
  let b := ∫s in 0..c.period, |c.force s|
  have lp := c.period_pos
  have bp : 0 ≤ b := intervalIntegral.integral_nonneg_of_forall lp.le (fun s => abs_nonneg (c.force s))
  change 4*(max 0 x)^3 ≤ 27*c.period*b^2
  by_cases hx : 0 < x
  · rw [max_eq_right hx.le]
    let a := Real.sqrt (x/(3*c.period))
    have ha : 0<a := Real.sqrt_pos.mpr (by positivity)
    have ha2 : a^2*(3*c.period)=x := by
      dsimp only [a]
      rw [Real.sq_sqrt (by positivity),div_mul_cancel₀ _ (by positivity)]
    have est := (c.stressMass_le_regularized a).trans (c.regularizedStress_integral_le ha)
    change c.stressMass ≤ a^2*c.period+3*c.energy+b/a at est
    have hb : (2*x/3)*a ≤ b := by
      apply (le_div_iff₀ ha).mp
      dsimp only [x] at *
      linarith only [est,ha2]
    have hs := (sq_le_sq₀ (by positivity) bp).mpr hb
    have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0≤27*c.period)
    have he := congrArg (fun z:ℝ => 4*x^2*z) ha2
    nlinarith only [hm,he]
  · rw [max_eq_left (le_of_not_gt hx)]
    norm_num only [zero_pow, mul_zero]
    positivity

theorem stressMass_excess_cube :
    4*(max 0 (c.stressMass-3*c.energy))^3 ≤ 27*c.period^2*c.dissipation := by
  have cs := LengthGrowth.interval_integral_mul_sq_le c.force_continuous.abs
    (continuous_const (y:=(1:ℝ))) c.period_pos.le
  simp only [mul_one,sq_abs,one_pow,intervalIntegral.integral_const,sub_zero,smul_eq_mul] at cs
  change (∫s in 0..c.period, |c.force s|)^2 ≤ c.dissipation*c.period at cs
  have lp := c.period_pos
  have hh := mul_le_mul_of_nonneg_left cs (by positivity : 0 ≤ 27*c.period)
  linarith only [c.stressMass_excess_cube_force,hh]

end LengthGrowth.ClosedFrenetCurve

namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- Scale-invariant whole-stress mass control on every actual time slice. -/
theorem physicalStressMass_excess_cube {t : ℝ} (ht : 0 ≤ t) :
    let p := (c.regularPositionAt ht).closedFrenetCurve
    4*(max 0 (p.stressMass-3*c.energy t))^3 ≤ 27*(c.length t)^2*c.dissipation t := by
  let p := (c.regularPositionAt ht).closedFrenetCurve
  have he : p.energy=c.energy t := (c.regularPositionAt ht).closedFrenetCurve_energy
  have hd : p.dissipation=c.dissipation t := (c.regularPositionAt ht).closedFrenetCurve_dissipation
  have hl : p.period=c.length t := rfl
  simpa only [he,hd,hl] using p.stressMass_excess_cube
end LengthGrowth.ActualFlow.ForwardImmersion

#print axioms LengthGrowth.ClosedFrenetCurve.regularizedStress_integral_le
#print axioms LengthGrowth.ClosedFrenetCurve.stressMass_excess_cube_force
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.physicalStressMass_excess_cube
