import LengthGrowth.OscillatorTime
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section
namespace LengthGrowth.OscillatorMean
open Set Real MeasureTheory
set_option maxHeartbeats 650000

private def pair (c r t : ℝ) := rawTerm c r (r*cos t)+rawTerm c r (-(r*cos t))

private theorem raw_continuous {c r : ℝ} (hd : 0<orbitOffset c r) : Continuous (rawTerm c r) := by
  unfold rawTerm
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    exact (sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg _) hd)).ne'

private theorem pair_cont {c r : ℝ} (hd : 0<orbitOffset c r) : Continuous (pair c r) :=
  ((raw_continuous hd).comp (continuous_cos.const_mul r)).add
    ((raw_continuous hd).comp (continuous_cos.const_mul r).neg)

private theorem numerator_pair {c r : ℝ} (hd : 0<orbitOffset c r) :
    numerator c r=∫ t in 0..π/2,pair c r t := by
  let f : ℝ → ℝ := fun t => rawTerm c r (r*cos t)
  have cf : Continuous f := (raw_continuous hd).comp (continuous_cos.const_mul r)
  have cg : Continuous (fun θ => rawTerm c r (-(r*cos θ))) :=
    (raw_continuous hd).comp (continuous_cos.const_mul r).neg
  have flip : (fun t => f (π-t))=(fun t => rawTerm c r (-(r*cos t))) := by
    funext t
    simp [f,cos_pi_sub]
  have sub := intervalIntegral.integral_comp_sub_left (a:=0) (b:=π/2) f π
  rw [flip,show π-π/2=π/2 by ring,sub_zero] at sub
  have eq : (fun t => anglePosition c r t*inverseRadical c r t)=f := by
    funext t
    dsimp [f,rawTerm,anglePosition,inverseRadical]
    rw [show c+r*cos t+c=2*c+r*cos t by ring]
    ring
  dsimp only [numerator]
  rw [eq]
  change _=∫ t in 0..π/2,f t+rawTerm c r (-(r*cos t))
  rw [intervalIntegral.integral_add (cf.intervalIntegrable _ _) (cg.intervalIntegrable _ _),sub,
    intervalIntegral.integral_add_adjacent_intervals (cf.intervalIntegrable _ _) (cf.intervalIntegrable _ _)]

private theorem small_numerator {c r : ℝ} (hc : 0<c) (hc' : c≤1/2) (hr : 0<r)
    (turn : 2*c*r^2=1+c-2*c^3) (hd : 0<orbitOffset c r) :
    (c/r)*(4*π/385)<numerator c r := by
  have ep : pair c r=(fun θ => (c/r)*angular c θ) := by
    funext θ
    rw [show pair c r θ=_ from low_pair hc hc' hr turn]
    dsimp [angular]; ring
  rw [numerator_pair hd,ep,intervalIntegral.integral_const_mul]
  exact mul_lt_mul_of_pos_left (angular_mean_lower hc.le hc') (div_pos hc hr)

private theorem central_raw {c r v : ℝ} (hc : 1/2≤c) (hc' : c≤1)
    (hr : 0<r) (hr' : r≤2) (hd : 0<orbitOffset c r) (hv : |v|≤1/4) :
    (1/20:ℝ)≤rawTerm c r v := by
  obtain ⟨hvl,hvu⟩ := abs_le.mp hv
  have sqc := pow_le_pow_left₀ (show 0≤c by linarith) hc' 2
  have sqr := pow_le_pow_left₀ hr.le hr' 2
  have sqv := pow_le_pow_left₀ (show 0≤2*c+v by linarith)
    (show 2*c+v≤9/4 by linarith) 2
  have pos : 0<(2*c+v)^2+orbitOffset c r := by positivity
  have sub : (2*c+v)^2+orbitOffset c r≤25 := by dsimp [orbitOffset]; nlinarith only [sqc,sqr,sqv]
  have hs : √((2*c+v)^2+orbitOffset c r)≤5 := by
    nlinarith only [sq_sqrt pos.le,sub,sqrt_nonneg ((2*c+v)^2+orbitOffset c r)]
  exact (le_div_iff₀ (sqrt_pos.mpr pos)).mpr (by linarith only [hs,hc,hvl])

private theorem large_numerator {c r : ℝ} (hc : 1/2≤c) (hc' : c<1) (hr : 0<r)
    (turn : 2*c*r^2=1+c-2*c^3) (hd : 0<orbitOffset c r) :
    (1/80:ℝ)≤numerator c r := by
  have hr' : r≤2 := by
    have ha := mul_nonneg (show 0≤2*c-1 by linarith) (sq_nonneg r)
    have h3 := pow_nonneg (show 0≤c by linarith) 3
    nlinarith only [turn,hr,ha,h3,hc']
  let s := π/2-1/8
  have hs : 0≤s := by dsimp [s]; linarith [Real.pi_gt_three]
  have hs' : s≤π/2 := by dsimp [s]; linarith
  have cp := pair_cont hd
  have lo := intervalIntegral.integral_nonneg (μ:=volume) hs (f:=pair c r)
    (fun θ hθ => high_pair hc (mul_nonneg hr.le (cos_nonneg_of_mem_Icc
      ⟨by linarith [pi_pos,hθ.1],hθ.2.trans hs'⟩))
      (by simpa using mul_le_mul_of_nonneg_left (cos_le_one θ) hr.le) hd)
  have point (θ : ℝ) (hθ : θ∈Icc s (π/2)) : (1/10:ℝ)≤pair c r θ := by
    have hcos := abs_cos_sub_cos_le θ (π/2)
    rw [cos_pi_div_two,sub_zero,abs_of_nonpos (sub_nonpos.mpr hθ.2)] at hcos
    have absY : |r*cos θ|≤1/4 := by
      rw [abs_mul,abs_of_pos hr]
      have e : |cos θ|≤1/8 := by dsimp [s] at hθ; linarith [hθ.1]
      calc r*|cos θ|≤2*(1/8:ℝ) := mul_le_mul hr' e (abs_nonneg _) (by norm_num)
           _ = _ := by norm_num
    have a := central_raw hc hc'.le hr hr' hd absY
    have b := central_raw hc hc'.le hr hr' hd (v:=-(r*cos θ)) (by rwa [abs_neg])
    dsimp only [pair]; linarith
  have hi := intervalIntegral.integral_mono_on (μ:=volume) hs'
    (continuous_const.intervalIntegrable s (π/2)) (cp.intervalIntegrable s (π/2)) point
  rw [intervalIntegral.integral_const] at hi
  have sum := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (cp.intervalIntegrable 0 s) (cp.intervalIntegrable s (π/2))
  rw [numerator_pair hd,← sum]
  change (π/2-s)*(1/10)≤_ at hi
  have len : π/2-s=1/8 := by dsimp [s];ring
  rw [len] at hi
  linarith only [hi,lo]

theorem mean_floor {c r A : ℝ} (hr : 0<r) (hV : quarticPotential (c+r)=quarticPotential (c-r))
    (hA : 2≤A) (hrA : r≤A) :
    1/(1000*(1+A)^3) ≤ periodMean c r := by
  obtain ⟨hc,hc',turn,hd⟩ := turning_parameters hr hV
  have hdp : 0<orbitOffset c r := by linarith
  obtain ⟨hD,hDu⟩ := period_bounds hd
  change 0<4*denominator c r at hD
  change 4*denominator c r≤8*π at hDu
  have ad : 0<1+A := by linarith
  apply (le_div_iff₀ (show 0<denominator c r by linarith)).mpr
  rw [show 1/(1000*(1+A)^3)*denominator c r=denominator c r/(1000*(1+A)^3) by ring]
  apply (div_le_iff₀ (show 0<1000*(1+A)^3 by positivity)).mpr
  by_cases small : c≤1/2
  · have low := small_numerator hc small hr turn hdp
    have lown : 4*c*π < 385*r*numerator c r := by
      have e := mul_lt_mul_of_pos_left low (show 0<385*r by positivity)
      field_simp [hr.ne'] at e
      linarith only [e]
    have r2 := pow_le_pow_left₀ hr.le hrA 2
    have c3 := pow_le_pow_left₀ hc.le hc'.le 3
    have c2 := pow_le_pow_left₀ hc.le hc'.le 2
    have one : 1≤2*c*(1+A^2) := by
      nlinarith only [turn,mul_nonneg hc.le (sub_nonneg.mpr r2),
        mul_nonneg hc.le (show 0≤1-c^2 by linarith only [c2]),hc]
    have N : 0<numerator c r := lt_trans (by positivity) low
    have D0 : denominator c r≤2*π := by linarith only [hDu]
    have ea := mul_le_mul_of_nonneg_left one (show 0≤2*π by positivity)
    have eb := mul_le_mul_of_nonneg_right lown.le (show 0≤1+A^2 by positivity)
    have ec : 385*r*(1+A^2) ≤ 1000*(1+A)^3 := by
      have hmul := mul_le_mul_of_nonneg_right hrA (show 0≤1+A^2 by positivity)
      nlinarith only [hmul,hA,pow_nonneg (show 0≤A by linarith) 2,
        pow_nonneg (show 0≤A by linarith) 3]
    nlinarith only [ea,eb,mul_le_mul_of_nonneg_right ec N.le,D0]
  · have N := large_numerator (le_of_not_ge small) hc' hr turn hdp
    have pc := Real.pi_lt_four
    have big : (1+2:ℝ)^3 ≤ (1+A)^3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
    nlinarith only [N,hDu,pc,mul_nonneg (sub_nonneg.mpr N) (pow_nonneg ad.le 3),big]

theorem global_c2_explicit_window_lower (z : ℝ → ℝ) (hz : ContDiff ℝ 2 z)
    (eqn : ∀ t,deriv (deriv z) t=-(z t)^3/2+z t/4+1/4)
    {A : ℝ} (hA : 2≤A) (bound : ∀ t,|z t|≤A) (s T : ℝ) (hT : 0<T) :
    1/(1000*(1+A)^3)-16*π*A/T ≤ (∫ t in s..s+T,z t)/T := by
  have hAp : 0<A := by linarith
  rcases global_c2_time_quadrature z hz eqn with he|⟨c,r,h⟩
  · rw [show z=(fun _ => (1:ℝ)) from funext he,intervalIntegral.integral_const]
    simp only [add_sub_cancel_left,smul_eq_mul,mul_one,div_self hT.ne']
    have big : (1:ℝ)^3≤(1+A)^3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
    have base : 1/(1000*(1+A)^3)≤1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith only [base,show 0≤16*π*A/T by positivity]
  · obtain ⟨t,_,ht,_⟩ := h.turning_plus
    have hrA : r≤A := by
      have peak := (le_abs_self (z t)).trans (bound t)
      rw [ht] at peak
      linarith [h.center_pos]
    have hm := mean_floor h.radius_pos h.equal_potential hA hrA
    have hw := (abs_le.mp (h.window bound s T hT)).1
    linarith

end LengthGrowth.OscillatorMean

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms `LengthGrowth.OscillatorMean.global_c2_explicit_window_lower) do
    unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains ax do
      throwError "Unexpected axiom {ax}"
  logInfo "OSCILLATOR_FLOOR_AUDIT: explicit positive mean floor and finite-window lower bound for actual C2 solutions."
