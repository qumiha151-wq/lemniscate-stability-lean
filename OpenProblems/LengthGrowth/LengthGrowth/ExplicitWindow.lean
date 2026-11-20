import LengthGrowth.PeriodicWindowGap
import LengthGrowth.OscillatorStability
import LengthGrowth.OscillatorUnitInterval
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section
open Set MeasureTheory Real
open scoped ContDiff
namespace LengthGrowth.ExplicitWindow
open PeriodicWindowGap

def m : ℝ := 1/(1000*161^3)
def M : ℝ := 512/m^2
def A : ℝ := 20*M
def T : ℝ := 256*π*A/m
def K : ℝ := 2*(A+1)^2+2
def τ : ℝ := m/16*exp (-(K*T))
def ε : ℝ := gapEpsilon m T τ

theorem m_pos : 0<m := by norm_num [m]
theorem m_le_one : m≤1 := by norm_num [m]
theorem M_large : 8≤M := by norm_num [M,m]
theorem A_large : 160≤A := by unfold A; linarith only [M_large]
theorem T_large : 1≤T := by
  have hπ : (1:ℝ)≤π := by linarith only [Real.two_le_pi]
  unfold T
  apply (le_div_iff₀ m_pos).mpr
  nlinarith only [mul_le_mul hπ A_large (by norm_num : (0:ℝ)≤160) pi_pos.le,m_le_one]
theorem tau_pos : 0<τ := mul_pos (div_pos m_pos (by norm_num)) (exp_pos _)
theorem eps_pos : 0<ε := gapEpsilon_pos m_pos (by linarith only [T_large]) tau_pos
theorem eps_lt_half : ε<1/2 := gapEpsilon_lt_half _ _ _

private theorem time_error : 16*π*A/T=m/16 := by
  unfold T
  have ha : A≠0 := ne_of_gt (by linarith only [A_large])
  field_simp [ha,pi_ne_zero,m_pos.ne']
  ring

private theorem residual_eq (u : ℝ → ℝ) : PeriodicWindowGap.residual u = OscillatorLocal.residual u := by
  funext y
  dsimp [PeriodicWindowGap.residual,PeriodicWindowGap.force,OscillatorLocal.residual]
  ring

def Ode (z : ℝ → ℝ) : Prop := ∀ t, deriv (deriv z) t=QuarticStability.force (z t)

/-- Assemble unit-scale initial data, residual stability and exact-orbit
time averages into the comparison used by the scalar periodic gap. -/
theorem from_exact_oscillators
    (solve : ∀ x b v : ℝ, ∃ z : ℝ → ℝ, ContDiff ℝ ∞ z ∧ Ode z ∧ z x=b ∧ deriv z x=v)
    (averages : ∀ (z : ℝ → ℝ), ContDiff ℝ ∞ z → Ode z → ∀ B : ℝ,
      2≤B → (∀ t, |z t|≤B) → ∀ x : ℝ,
      1/(1000*(1+B)^3)-16*π*B/T ≤ (∫ s in x..x+T,z s)/T) :
    OscillatorWindowComparison m T (τ^2/T) := by
  intro u hu x hmass hsmall
  have dmass : ∀ C : ℝ, mass 1 (fun y => u y^2+PeriodicWindowGap.residual u y^2) x ≤ C →
        (∫ s in x..x+1,OscillatorLocal.unitDensity u s) ≤ C := by
    intro C hyp
    simpa only [mass_eq_interval,residual_eq,OscillatorLocal.unitDensity] using hyp
  obtain ⟨z,hz,hode,hpos,hvel⟩ := solve x (u x) (deriv u x)
  have data : ∀ t, |z t|≤A ∧ |deriv z t|≤60*M^2 := fun t =>
    (OscillatorLocal.exact_orbit_from_unit_interval hu (by linarith only [M_large] : 1≤M)
      (dmass _ hmass) hz hode hpos hvel t).2
  have hd := (contDiff_infty_iff_deriv.mp hu).2
  have hz' := (contDiff_infty_iff_deriv.mp hz).2
  have dc : Continuous (PeriodicWindowGap.residual u) := by
    unfold PeriodicWindowGap.residual PeriodicWindowGap.force
    apply Continuous.sub _ continuous_const
    exact (((contDiff_infty_iff_deriv.mp hd).2.continuous).add
      ((hu.continuous.pow 3).const_mul _)).sub (hu.continuous.div_const _)
  have du := hu.differentiable (by simp)
  have dz := hz.differentiable (by simp)
  have dp (s) : HasDerivAt (deriv u) (QuarticStability.force (u s)+PeriodicWindowGap.residual u s) s := by
    rw [show QuarticStability.force (u s)+PeriodicWindowGap.residual u s=deriv (deriv u) s by
      unfold QuarticStability.force PeriodicWindowGap.residual PeriodicWindowGap.force
      ring]
    exact (hd.differentiable (by simp) s).hasDerivAt
  have dq (s) : HasDerivAt (deriv z) (QuarticStability.force (z s)) s := by
    rw [← hode s]
    exact (hz'.differentiable (by simp) s).hasDerivAt
  have exponent : 3+2*(60*M^2)≤2*K := by
    dsimp [K,A]
    nlinarith only [sq_nonneg M,M_large]
  have approx := QuarticStability.window_bound T_large (div_nonneg m_pos.le (by norm_num : (0:ℝ)≤16))
    exponent dc (fun s => (du s).hasDerivAt) dp (fun s => (dz s).hasDerivAt) dq
    hpos.symm hvel.symm (fun s _ => (data s).2) (by simpa only [mass_eq_interval,τ] using hsmall)
  have Tpos : 0<T := by linarith only [T_large]
  have diff : (∫ t in x..x+T,z t)/T-m/16 ≤ window T u x := by
    have hh := intervalIntegral.integral_mono_on (μ:=volume)
      (show x≤x+T by linarith) ((hz.continuous.sub continuous_const).intervalIntegrable x (x+T))
      (hu.continuous.intervalIntegrable x (x+T)) (fun y hy => by
        have a := (abs_le.mp (approx y hy)).1
        change z y-m/16≤u y
        linarith)
    change (∫ y in x..x+T,z y-m/16) ≤ ∫ y in x..x+T,u y at hh
    rw [intervalIntegral.integral_sub (hz.continuous.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _),intervalIntegral.integral_const] at hh
    simp only [add_sub_cancel_left,smul_eq_mul] at hh
    rw [window,mass_eq_interval]
    apply (le_div_iff₀ Tpos).mpr
    rw [sub_mul,div_mul_cancel₀ _ Tpos.ne']
    linarith only [hh]
  constructor
  · have lower := averages z hz hode A (by linarith only [A_large]) (fun s => (data s).1) x
    rw [time_error] at lower
    have ha : 0≤A := by linarith only [A_large]
    linarith only [diff,lower,show (0:ℝ)≤1/(1000*(1+A)^3) by positivity]
  · intro hsmallMass
    have bound s : |z s|≤160 := by
      have h := (OscillatorLocal.exact_orbit_from_unit_interval hu (by norm_num : (1:ℝ)≤8)
        (dmass 8 hsmallMass) hz hode hpos hvel s).2.1
      linarith
    have lower := averages z hz hode 160 (by norm_num) bound x
    have coerc : 16*π*160/T ≤ m/16 := by
      rw [← time_error]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left A_large (by positivity)) Tpos.le
    have hc : (1:ℝ)/(1000*(1+160:ℝ)^3)=m := by norm_num [m]
    rw [hc] at lower
    linarith

end LengthGrowth.ExplicitWindow
