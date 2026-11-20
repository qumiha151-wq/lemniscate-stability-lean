import LengthGrowth.OscillatorPeriodNumerator
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Conservation and explicit amplitude and speed bounds for the exact oscillator. -/
noncomputable section
open scoped ContDiff
open LengthGrowth.OscillatorMean
namespace LengthGrowth.OscillatorLocal

def oscillatorEnergy (z : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv z t ^ 2 / 2 + quarticPotential (z t)

theorem oscillatorEnergy_constant {z : ℝ → ℝ} (hz : ContDiff ℝ ∞ z)
    (ode : ∀ t, deriv (deriv z) t = -(z t)^3/2+z t/4+1/4) (t x : ℝ) :
    oscillatorEnergy z t = oscillatorEnergy z x := by
  have hd (y : ℝ) : HasDerivAt (oscillatorEnergy z) 0 y := by
    have hdz := (hz.differentiable (by simp) y).hasDerivAt
    have hddz := ((contDiff_infty_iff_deriv.mp hz).2.differentiable (by simp) y).hasDerivAt
    rw [ode y] at hddz
    have pot := ((((hdz.pow 4).sub (hdz.pow 2)).sub (hdz.const_mul 2)).div_const 8)
    have e := ((hddz.pow 2).div_const 2).add pot
    convert! e using 1
    dsimp
    ring
  exact is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt)
    (fun y => (hd y).deriv) t x

private theorem potential_lower (s : ℝ) : -1 ≤ quarticPotential s := by
  unfold quarticPotential
  nlinarith only [sq_nonneg (s^2-1), sq_nonneg (s-1)]

private theorem potential_large {s : ℝ} (hs : 4 ≤ |s|) :
    s^4/16 ≤ quarticPotential s := by
  have hsq := mul_self_le_mul_self (by norm_num : 0 ≤ (4:ℝ)) hs
  have hh := mul_nonneg (show 0 ≤ s^2-16 by nlinarith [sq_abs s])
    (sq_nonneg s)
  unfold quarticPotential
  nlinarith only [hh,sq_nonneg (s-1),hsq,sq_abs s]

/-- Initial data bounds control the conserved energy and the orbit at every time. -/
theorem oscillator_orbit_data {z : ℝ → ℝ} (hz : ContDiff ℝ ∞ z)
    (ode : ∀ t, deriv (deriv z) t = -(z t)^3/2+z t/4+1/4)
    {x M : ℝ} (hM : 1≤M) (hx : |z x|≤10*M) (hv : |deriv z x|≤16*M^2) (t : ℝ) :
    oscillatorEnergy z t ≤ 1400*M^4 ∧ |z t| ≤ 20*M ∧ |deriv z t| ≤ 60*M^2 := by
  have h0 : 0 ≤ M := by linarith
  have M4 : M ≤ M^4 := by
    calc
      M = M*1 := by ring
      _ ≤ M*M^3 := mul_le_mul_of_nonneg_left (one_le_pow₀ hM) h0
      _ = _ := by ring
  have M41 : 1 ≤ M^4 := hM.trans M4
  have zp := pow_le_pow_left₀ (abs_nonneg (z x)) hx 4
  have vp := pow_le_pow_left₀ (abs_nonneg (deriv z x)) hv 2
  rw [sq_abs] at vp
  rw [(show Even 4 by decide).pow_abs] at zp
  have energy : oscillatorEnergy z t ≤ 1400*M^4 := by
    rw [oscillatorEnergy_constant hz ode t x]
    dsimp only [oscillatorEnergy,quarticPotential]
    nlinarith only [zp,vp,sq_nonneg (z x),neg_le_abs (z x),hx,M4,M41]
  refine ⟨energy,?_,?_⟩
  · by_contra! h
    have hlarge := potential_large (show 4 ≤ |z t| by linarith)
    have pow_lt := pow_lt_pow_left₀ h (show 0 ≤ 20*M by positivity) (by norm_num : 4 ≠ 0)
    have ha : |z t|^4=(z t)^4 := (show Even 4 by decide).pow_abs _
    rw [ha] at pow_lt
    unfold oscillatorEnergy at energy
    nlinarith only [energy,hlarge,sq_nonneg (deriv z t),pow_lt,M41]
  · by_contra! h
    have pow_lt := pow_lt_pow_left₀ h (show 0 ≤ 60*M^2 by positivity) (by norm_num : 2 ≠ 0)
    rw [sq_abs] at pow_lt
    unfold oscillatorEnergy at energy
    nlinarith only [energy,potential_lower (z t),pow_lt,M41]

#print axioms oscillatorEnergy_constant
#print axioms oscillator_orbit_data
end LengthGrowth.OscillatorLocal
