import LengthGrowth.ElasticStress
import LengthGrowth.IntervalL2
import LengthGrowth.IntervalOscillation
import Mathlib.Tactic.Positivity

/-! Actual integral estimates for the closed Frenet curve. These are
derived from its geometry; no elastic-stress coercivity bound is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace LengthGrowth.ClosedFrenetCurve

variable (c : LengthGrowth.ClosedFrenetCurve)

def energy : ℝ := (∫ s in 0..c.period, c.curvature s ^ 2) / 2
def dissipation : ℝ := ∫ s in 0..c.period, c.force s ^ 2
def absoluteCurvature : ℝ := ∫ s in 0..c.period, |c.curvature s|
def curvatureGradientSquare : ℝ := ∫ s in 0..c.period, c.curvature₁ s ^ 2

theorem tangent_displacement_bound {s : ℝ} (hs : s ∈ Icc 0 c.period) :
    ‖c.tangent s - c.tangent 0‖ ≤ c.absoluteCurvature := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => c.tangent_deriv u)
    (((Complex.continuous_ofReal.comp c.curvature_continuous).mul
      (continuous_const.mul c.tangent_continuous)).intervalIntegrable 0 s)
  rw [← hi]
  calc
    _ ≤ ∫ u in 0..s, ‖(c.curvature u : ℂ) * (Complex.I * c.tangent u)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hs.1
    _ = ∫ u in 0..s, |c.curvature u| := by
      congr 1
      funext u
      simp [c.tangent_unit]
    _ ≤ c.absoluteCurvature := by
      exact intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
        (Filter.Eventually.of_forall (fun u => abs_nonneg _))
        (c.curvature_continuous.abs.intervalIntegrable _ _)

/-- The weak total-turn bound needed by the coercivity proof follows
directly from closure and FTC. No formal Fenchel theorem is imported. -/
theorem one_le_absoluteCurvature : 1 ≤ c.absoluteCurvature := by
  have hi : (∫ s in 0..c.period, c.tangent 0 - c.tangent s) =
      c.period • c.tangent 0 := by
    rw [intervalIntegral.integral_sub
      (continuous_const.intervalIntegrable _ _) (c.tangent_continuous.intervalIntegrable _ _),
      intervalIntegral.integral_const, c.tangent_integral_zero]
    simp
  have hn := intervalIntegral.norm_integral_le_integral_norm (c.period_pos.le)
    (f := fun s => c.tangent 0-c.tangent s) (μ := volume)
  rw [hi, norm_smul, c.tangent_unit] at hn
  simp only [Real.norm_eq_abs, abs_of_pos c.period_pos, mul_one] at hn
  have hm : (∫ s in 0..c.period, ‖c.tangent 0-c.tangent s‖) ≤
      c.period*c.absoluteCurvature := by
    calc
      _ ≤ ∫ s in 0..c.period, c.absoluteCurvature := by
        apply intervalIntegral.integral_mono_on c.period_pos.le
          ((continuous_const.sub c.tangent_continuous).norm.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
        intro s hs
        change ‖c.tangent 0-c.tangent s‖ ≤ c.absoluteCurvature
        rw [norm_sub_rev]
        exact c.tangent_displacement_bound hs
      _ = _ := by simp
  have h := hn.trans hm
  nlinarith [c.period_pos]

theorem weak_energy_length_bound : (1:ℝ)/2 ≤ c.energy*c.period := by
  have hcs := LengthGrowth.interval_integral_mul_sq_le
    c.curvature_continuous.abs (continuous_const (y := (1:ℝ))) c.period_pos.le
  simp only [mul_one, sq_abs, one_pow, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul, mul_one] at hcs
  change c.absoluteCurvature^2 ≤
    (∫ s in 0..c.period, c.curvature s^2)*c.period at hcs
  have hA := c.one_le_absoluteCurvature
  dsimp [energy]
  nlinarith

theorem energy_pos : 0 < c.energy := by
  have h := c.weak_energy_length_bound
  nlinarith [c.period_pos]

theorem curvature_gradient_identity : c.curvatureGradientSquare =
    (∫ s in 0..c.period, c.curvature s^4)/2 -
      (∫ s in 0..c.period, c.curvature s*c.force s) := by
  have hk := c.curvature_continuous
  have hk₁ := c.curvature₁_continuous
  have hk₂ := c.curvature₂_continuous
  have hd : ∀ s, HasDerivAt (fun u => c.curvature u*c.curvature₁ u)
      (c.curvature₁ s*c.curvature₁ s+c.curvature s*c.curvature₂ s) s := by
    intro s
    exact (c.curvature_deriv s).mul (c.curvature₁_deriv s)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hd s) (((hk₁.mul hk₁).add (hk.mul hk₂)).intervalIntegrable 0 c.period)
  have hp : c.curvature c.period = c.curvature 0 := by
    simpa using c.curvature_periodic 0
  have hp₁ : c.curvature₁ c.period = c.curvature₁ 0 := by
    simpa using c.curvature₁_periodic 0
  rw [hp, hp₁, sub_self, intervalIntegral.integral_add
    (f := fun s => c.curvature₁ s*c.curvature₁ s)
    (g := fun s => c.curvature s*c.curvature₂ s)
    ((hk₁.mul hk₁).intervalIntegrable _ _) ((hk.mul hk₂).intervalIntegrable _ _)] at hi
  have heq : (fun s => c.curvature s*c.force s) =
      (fun s => c.curvature s*c.curvature₂ s+(1/2:ℝ)*c.curvature s^4) := by
    funext s
    dsimp [force]
    ring
  rw [heq, intervalIntegral.integral_add
    (f := fun s => c.curvature s*c.curvature₂ s)
    (g := fun s => (1/2:ℝ)*c.curvature s^4)
    ((hk.mul hk₂).intervalIntegrable _ _)
    (((hk.pow 4).const_mul (1/2)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]
  dsimp [curvatureGradientSquare]
  simp only [← pow_two] at hi
  linarith

theorem curvature_gradient_nonneg : 0 ≤ c.curvatureGradientSquare :=
  intervalIntegral.integral_nonneg_of_forall c.period_pos.le (fun s => sq_nonneg (c.curvature₁ s))

theorem dissipation_nonneg : 0 ≤ c.dissipation :=
  intervalIntegral.integral_nonneg_of_forall c.period_pos.le (fun s => sq_nonneg (c.force s))

theorem curvature_force_integral_bound :
    |∫ s in 0..c.period, c.curvature s*c.force s| ≤
      Real.sqrt (2*c.energy*c.dissipation) := by
  have hi := LengthGrowth.interval_integral_mul_sq_le
    c.curvature_continuous c.force_continuous c.period_pos.le
  have he : (∫ s in 0..c.period, c.curvature s^2)=2*c.energy := by
    dsimp [energy]
    ring
  rw [he] at hi
  change (∫ s in 0..c.period, c.curvature s*c.force s)^2 ≤
    2*c.energy*c.dissipation at hi
  exact Real.abs_le_sqrt hi

theorem curvature_gradient_bound {M : ℝ} (hM : 0 ≤ M)
    (hmax : ∀ s ∈ Icc 0 c.period, |c.curvature s| ≤ M) :
    c.curvatureGradientSquare ≤ c.energy*M^2 +
      Real.sqrt (2*c.energy*c.dissipation) := by
  have hk := c.curvature_continuous
  have hfour : (∫ s in 0..c.period, c.curvature s^4) ≤
      M^2*(∫ s in 0..c.period, c.curvature s^2) := by
    calc
      _ ≤ ∫ s in 0..c.period, M^2*c.curvature s^2 := by
        apply intervalIntegral.integral_mono_on c.period_pos.le
          ((hk.pow 4).intervalIntegrable _ _) (((hk.pow 2).const_mul (M^2)).intervalIntegrable _ _)
        intro s hs
        change c.curvature s^4 ≤ M^2*c.curvature s^2
        have hsM := sq_le_sq₀ (abs_nonneg (c.curvature s)) hM |>.mpr (hmax s hs)
        simp only [sq_abs] at hsM
        nlinarith [mul_nonneg (sq_nonneg (c.curvature s)) (sub_nonneg.mpr hsM)]
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hf := c.curvature_force_integral_bound
  rw [c.curvature_gradient_identity]
  dsimp [energy] at *
  have hn := neg_le_abs (∫ s in 0..c.period, c.curvature s*c.force s)
  nlinarith

theorem curvature_pointwise_bound {s₀ : ℝ} (hs₀ : s₀ ∈ Icc 0 c.period) :
    c.curvature s₀^2 ≤ 4*c.energy^2 +
      2*Real.sqrt (2*c.energy)*Real.sqrt c.curvatureGradientSquare := by
  let J : ℝ := ∫ s in 0..c.period, |2*c.curvature s*c.curvature₁ s|
  have hk := c.curvature_continuous
  have hk₁ := c.curvature₁_continuous
  have hd : ∀ s, HasDerivAt (fun u => c.curvature u^2)
      (2*c.curvature s*c.curvature₁ s) s := by
    intro s
    convert! (c.curvature_deriv s).pow 2 using 1
    simp
  have hb (s : ℝ) (hs : s ∈ Icc 0 c.period) :
      c.curvature s₀^2 ≤ c.curvature s^2+J := by
    have h := LengthGrowth.interval_oscillation_le hd
      ((hk.const_mul 2).mul hk₁) hs₀ hs
    change |c.curvature s₀^2-c.curvature s^2| ≤ J at h
    linarith [le_abs_self (c.curvature s₀^2-c.curvature s^2)]
  have hm := intervalIntegral.integral_mono_on
    (μ := volume)
    (f := fun _ => c.curvature s₀^2) (g := fun s => c.curvature s^2+J)
    c.period_pos.le
    (continuous_const.intervalIntegrable 0 c.period)
    (((hk.pow 2).add continuous_const).intervalIntegrable 0 c.period) hb
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    (f := fun s => c.curvature s^2) (g := fun _ => J)
    ((hk.pow 2).intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const] at hm
  simp only [sub_zero, smul_eq_mul] at hm
  have heq : (∫ s in 0..c.period, c.curvature s^2)=2*c.energy := by
    dsimp [energy]
    ring
  rw [heq] at hm
  have hJ : J ≤ 2*Real.sqrt (2*c.energy)*Real.sqrt c.curvatureGradientSquare := by
    have hcs := LengthGrowth.interval_integral_abs_mul_le hk hk₁ c.period_pos.le
    rw [heq] at hcs
    change (∫ s in 0..c.period, |c.curvature s*c.curvature₁ s|) ≤
      Real.sqrt (2*c.energy)*Real.sqrt c.curvatureGradientSquare at hcs
    have hj : J = 2*(∫ s in 0..c.period, |c.curvature s*c.curvature₁ s|) := by
      dsimp [J]
      rw [show (fun s => |2*c.curvature s*c.curvature₁ s|) =
          (fun s => 2*|c.curvature s*c.curvature₁ s|) by
        funext s
        rw [mul_assoc, abs_mul]
        norm_num]
      exact intervalIntegral.integral_const_mul _ _
    rw [hj]
    linarith
  have hw := c.weak_energy_length_bound
  have he := c.energy_pos
  have hscaled := mul_le_mul_of_nonneg_right hw (show 0 ≤ 4*c.energy by positivity)
  have hMJ := mul_le_mul_of_nonneg_left hJ c.period_pos.le
  nlinarith [c.period_pos]

end LengthGrowth.ClosedFrenetCurve

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`LengthGrowth).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"LengthGrowth stress-integral audit passed for {checked} declarations."
