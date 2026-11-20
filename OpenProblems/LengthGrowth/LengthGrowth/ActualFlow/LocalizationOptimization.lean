import LengthGrowth.ActualFlow.LocalizationClock

noncomputable section
open Filter
open scoped Topology
namespace LengthGrowth.ActualFlow

/-- Optimize the finite-time moment estimate at the endpoint, simultaneously
for every point whenever its radius is bounded by the same estimate. -/
theorem localization_optimization {B R : ℝ→ℝ} {C : ℝ}
    (clock : Tendsto (fun t => B t/(localizationScale t)^2) atTop (𝓝 0))
    (nonnegative : ∀t≥1,0≤R t)
    (estimate : ∀t≥1, ∀a : ℝ, 0<a → a≤1 →
      a*R t≤C-2*Real.log a+256*(a^4*t+a^2*B t)) :
    Tendsto (fun t => R t/(localizationScale t*Real.sqrt (Real.log (2+t)))) atTop (𝓝 0) := by
  have small : Tendsto (fun t : ℝ => Real.log t/localizationScale t) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/3)).tendsto_div_nhds_zero
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let K := 1024/ε+1
  have K1 : 1≤K := by dsimp [K]; linarith [show 0≤1024/ε by positivity]
  have Kp : 0<K := by linarith
  have K4 : 0<K^4 := by positivity
  have K2 : 0<K^2 := by positivity
  have epsK : 1024≤ε*K := by dsimp [K]; field_simp; linarith
  have fsmall := small.eventually_lt_const (show 0<1/K^4 by positivity)
  have fclock := clock.eventually_lt_const (show 0<1/K^2 by positivity)
  filter_upwards [fsmall,fclock,Real.tendsto_log_atTop.eventually_ge_atTop (max 1 C),
    localizationScale_grows.eventually_ge_atTop 1,eventually_ge_atTop (1:ℝ)] with t htime hclock hH hr ht
  let r := localizationScale t
  let H := Real.log t
  let z := Real.sqrt H
  have hp : 1≤H := (le_max_left _ _).trans hH
  have cp : C≤H := (le_max_right _ _).trans hH
  have tp : 0<t := by linarith
  have rp : 0<r := by change 1≤r at hr; linarith
  have Hpos : 0<H := by linarith
  have zp : 0<z := Real.sqrt_pos.mpr Hpos
  have z2 : z^2=H := Real.sq_sqrt Hpos.le
  have z1 : 1≤z := by nlinarith only [hp,z2,zp]
  have zH : z≤H := by nlinarith only [z2,sq_nonneg (z-1),z1]
  have rt : r^3=t := localizationScale_cube tp.le
  have growth : H*K^4≤r := by
    change H/r<1/K^4 at htime
    have h := (div_lt_div_iff₀ rp K4).mp htime
    linarith
  have budget : B t*K^2≤r^2 := by
    have h := (div_lt_div_iff₀ (sq_pos_of_pos rp) K2).mp hclock
    linarith
  have k4k : K≤K^4 := by simpa only [pow_one] using pow_le_pow_right₀ K1 (by norm_num : (1:ℕ)≤4)
  let a := K*z/r
  have ap : 0<a := by dsimp [a]; positivity
  have a1 : a≤1 := (div_le_one rp).mpr ((mul_le_mul k4k zH zp.le K4.le).trans (by linarith))
  have r1 : 1≤r := hr
  have rlet : r≤t := by
    rw [←rt]
    simpa only [pow_one] using pow_le_pow_right₀ r1 (by norm_num : (1:ℕ)≤3)
  have a_inv : t⁻¹≤a := by
    rw [←one_div]
    change 1/t≤K*z/r
    apply (div_le_div_iff₀ tp rp).mpr
    have p : 1≤K*z := by simpa only [one_mul] using mul_le_mul K1 z1 (by norm_num) Kp.le
    nlinarith only [mul_le_mul_of_nonneg_right p tp.le,rlet]
  have loga : -H≤Real.log a := by simpa [H] using Real.log_le_log (inv_pos.mpr tp) a_inv
  have tterm : a^4*t≤H := by
    calc
      a^4*t = H*(H*K^4)/r := by dsimp [a]; rw [←rt,←z2]; field_simp
      _ ≤ H := (div_le_iff₀ rp).mpr (mul_le_mul_of_nonneg_left growth Hpos.le)
  have bterm : a^2*B t≤H := by
    calc
      a^2*B t = H*(B t*K^2)/r^2 := by dsimp [a]; rw [←z2]; ring
      _ ≤ H := (div_le_iff₀ (sq_pos_of_pos rp)).mpr (mul_le_mul_of_nonneg_left budget Hpos.le)
  have est := estimate t ht a ap a1
  have araw : a*R t≤515*H := by linarith only [est,tterm,bterm,loga,cp]
  have aeq : a*r=K*z := by dsimp [a]; field_simp
  have final : R t<ε*(r*z) := by
    apply (mul_lt_mul_iff_right₀ ap).mp
    calc
      _ ≤ 515*H := araw
      _ < (ε*K)*H := by nlinarith only [mul_le_mul_of_nonneg_right epsK Hpos.le,Hpos]
      _ = a*(ε*(r*z)) := by rw [←z2]; linear_combination -(ε*z)*aeq
  have logmon := Real.log_le_log tp (show t≤2+t by linarith)
  have zmon := Real.sqrt_le_sqrt logmon
  have bigp : 0<r*Real.sqrt (Real.log (2+t)) := mul_pos rp (zp.trans_le zmon)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (nonnegative t ht) bigp.le)]
  apply (div_lt_iff₀ bigp).mpr
  exact final.trans_le (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left zmon rp.le) hε.le)

end LengthGrowth.ActualFlow
#print axioms LengthGrowth.ActualFlow.localization_optimization
