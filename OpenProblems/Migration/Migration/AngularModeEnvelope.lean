import Migration.AngularWienerBound
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Set MeasureTheory
namespace MigrationGeometry.AngularGauge

private theorem decay_square {y : ℝ} (hy : 0≤y) : 2*(1-Real.exp (-y))^2≤y := by
  let g := fun s : ℝ=>s-2*(1-Real.exp (-s))^2
  have dg (s : ℝ) : HasDerivAt g ((1-2*Real.exp (-s))^2) s := by
    have he := (hasDerivAt_id s).neg.exp
    apply ((hasDerivAt_id s).sub ((((he.const_sub 1).pow 2).const_mul 2))).congr_deriv
    dsimp; ring
  have mon : Monotone g := monotone_of_deriv_nonneg (fun x=>(dg x).differentiableAt)
    (fun x => (dg x).deriv ▸ sq_nonneg _)
  have z := mon hy
  dsimp [g] at z
  simp only [neg_zero,Real.exp_zero,sub_self,zero_pow (by decide : 2≠0),mul_zero] at z
  linarith

/-- Uniform-in-time bound for the integrated, weighted Fourier multiplier,
including the zero mode. -/
theorem mode_kernel {t n : ℝ} (ht : 0≤t) :
    (1+n^2)*(∫s in (0:ℝ)..t, Real.exp ((s-t)*n^4))≤t+Real.sqrt (t/2) := by
  let K := fun s : ℝ=> Real.exp ((s-t)*n^4)
  have ck : Continuous K := by dsimp [K]; fun_prop
  have le1 : (∫s in (0:ℝ)..t,K s)≤t := by
    have hh := intervalIntegral.integral_mono_on (μ:=volume) (f:=K) (g:=fun _=>1) ht
      (ck.intervalIntegrable ..) intervalIntegrable_const (fun x hx=>Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.2) (by positivity)))
    simpa using hh
  change (1+n^2)*(∫s in (0:ℝ)..t,K s)≤_
  by_cases nz : n=0
  · simp only [nz,zero_pow (by decide : 2≠0),add_zero,one_mul]
    linarith [Real.sqrt_nonneg (t/2)]
  have id (s : ℝ) : HasDerivAt K (K s*n^4) s := by
    apply (((((hasDerivAt_id s).sub_const t).mul_const (n^4)).exp)).congr_deriv; dsimp [K]; ring
  have ft := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=t) (fun s _=>id s)
    ((ck.mul continuous_const).intervalIntegrable ..)
  rw [intervalIntegral.integral_mul_const] at ft
  simp only [K,sub_self,zero_mul,Real.exp_zero,zero_sub] at ft
  have raw := decay_square (y:=t*n^4) (by positivity)
  rw [neg_mul] at ft
  let j := ∫s in (0:ℝ)..t,K s
  change j*n^4=1-Real.exp (-(t*n^4)) at ft
  rw [←ft] at raw
  have n4 : 0<n^4 := by nlinarith only [sq_pos_of_ne_zero (pow_ne_zero 2 nz)]
  have b : (2*(n^2*j)^2)*n^4≤t*n^4 := by nlinarith only [raw]
  have p := le_of_mul_le_mul_right b n4
  have sr := Real.sq_sqrt (show 0≤t/2 by positivity)
  have bound : n^2*j≤Real.sqrt (t/2) := by nlinarith only [p,sr,Real.sqrt_nonneg (t/2)]
  change j≤t at le1
  linarith only [bound,le1]

/-- Exact mode variation-of-constants bound for a complex Fourier
coefficient of a genuine differentiable solution. -/
theorem mode_solution {z f : ℝ→ℂ} {n t b : ℝ} (ht : 0≤t)
    (cf : Continuous f) (force : ∀s∈Icc 0 t,‖f s‖≤b)
    (ode : ∀s∈Icc 0 t,HasDerivAt z (-(n^4 : ℝ) • z s+f s) s) :
    (1+n^2)*‖z t‖ ≤ (1+n^2)*‖z 0‖+(t+Real.sqrt (t/2))*b := by
  let K := fun s : ℝ=> Real.exp ((s-t)*n^4)
  have ck : Continuous K := by dsimp [K]; fun_prop
  have d (s : ℝ) (hs : s∈Icc 0 t) :
      HasDerivAt (fun x => (K x:ℂ)*z x) ((K s:ℂ)*f s) s := by
    have ek := ((((hasDerivAt_id s).sub_const t).mul_const (n^4)).exp).ofReal_comp
    apply (ek.mul (ode s hs)).congr_deriv
    simp only [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_one,K,id_eq]; ring
  have ft := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=t)
    (fun s hs=>d s (by rwa [uIcc_of_le ht] at hs))
    (((Complex.continuous_ofReal.comp ck).mul cf).intervalIntegrable ..)
  have kt : K t=1 := by simp [K]
  rw [kt,Complex.ofReal_one,one_mul] at ft
  have kn (s : ℝ) : 0≤K s := (Real.exp_pos _).le
  have bound := (intervalIntegral.norm_integral_le_integral_norm (f:=fun s=>(K s:ℂ)*f s) ht).trans
    (intervalIntegral.integral_mono_on (μ:=volume) (g:=fun s=>K s*b) ht
      (((Complex.continuous_ofReal.comp ck).mul cf).norm.intervalIntegrable ..)
      ((ck.mul continuous_const).intervalIntegrable ..) (fun s hs=>by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (kn s)]
        exact mul_le_mul_of_nonneg_left (force s hs) (kn s)))
  rw [ft,intervalIntegral.integral_mul_const] at bound
  have q0 : K 0 ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
  have init : ‖(K 0:ℂ)*z 0‖≤‖z 0‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (kn 0)]
    exact mul_le_of_le_one_left (norm_nonneg _) q0
  have tri := norm_sub_le_norm_sub_add_norm_sub (z t) ((K 0:ℂ)*z 0) 0
  simp only [sub_zero] at tri
  have g : ‖z t‖≤‖z 0‖+(∫s in (0:ℝ)..t,K s)*b := by linarith only [tri,bound,init]
  have p := mul_le_mul_of_nonneg_left g (show 0≤1+n^2 by positivity)
  have q := mul_le_mul_of_nonneg_right (mode_kernel (n:=n) ht)
    ((norm_nonneg _).trans (force 0 (left_mem_Icc.mpr ht)))
  change (1+n^2)*(∫s in (0:ℝ)..t,K s)*b≤_ at q
  linarith only [p,q]

end MigrationGeometry.AngularGauge
#print axioms MigrationGeometry.AngularGauge.mode_solution
