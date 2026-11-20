import LengthGrowth.ActualFlow.ForwardDissipation
import LengthGrowth.ActualFlow.IntrinsicScaling
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The expanding one-turn circle as an actual forward normal flow. -/
noncomputable section
open Complex Set Filter MeasureTheory
open scoped ContDiff Topology ComplexConjugate
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.SharpCircle

abbrev unitCircle : ℝ → ℂ := circleMap 0 1

private theorem circleSpeed (u : ℝ) : speed unitCircle u = 1 := by
  simp [speed, norm_circleMap_zero]

private theorem circleTangent : tangent unitCircle = fun u => unitCircle u * I := by
  funext u
  simp [tangent, arcDerivative, circleSpeed u]

private theorem circleNormal (u : ℝ) : normal unitCircle u = -unitCircle u := by
  simp only [normal, circleTangent]
  calc
    I * (unitCircle u * I) = unitCircle u * (I * I) := by ring
    _ = _ := by simp

private theorem circleCurvature (u : ℝ) : curvature unitCircle u = 1 := by
  have hd := ((hasDerivAt_circleMap 0 1 u).mul_const I).deriv
  have hn : conj (unitCircle u) * unitCircle u = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_circleMap_zero]
    norm_num
  rw [curvature, circleSpeed, circleTangent, hd, div_one]
  have he : conj (unitCircle u * I) * (unitCircle u * I * I) = I := by
    rw [map_mul, Complex.conj_I]
    calc
      conj (unitCircle u) * -I * (unitCircle u * I * I) =
        -(conj (unitCircle u) * unitCircle u) * (I * I) * I := by ring
      _ = _ := by rw [hn, Complex.I_mul_I]; ring
  rw [he, Complex.I_im]

private theorem circleForce (u : ℝ) : force unitCircle u = 1/2 := by
  have hk : curvature unitCircle = fun _ => 1 := funext circleCurvature
  have hg : curvatureGradient unitCircle = fun _ => 0 := by
    funext z
    simp [curvatureGradient, arcDerivative, hk]
  simp [force, curvatureSecond, hg, arcDerivative, hk]

/-- Radius at physical time for the energy with coefficient one half. -/
def radius (r₀ t : ℝ) : ℝ := Real.sqrt (Real.sqrt (r₀^4 + 2*t))

theorem radius_initial {r₀ : ℝ} (hr : 0 < r₀) : radius r₀ 0 = r₀ := by
  rw [radius, mul_zero, add_zero, show (4:ℕ)=2*2 by decide, pow_mul,
    Real.sqrt_sq (sq_nonneg _), Real.sqrt_sq hr.le]

theorem radius_pos {r₀ t : ℝ} (hr : 0 < r₀) (ht : 0 ≤ t) : 0 < radius r₀ t := by
  apply Real.sqrt_pos_of_pos
  apply Real.sqrt_pos_of_pos
  positivity

theorem radius_fourth {r₀ t : ℝ} (hr : 0 < r₀) (ht : 0 ≤ t) :
    radius r₀ t ^ 4 = r₀^4+2*t := by
  have h : 0 ≤ r₀^4+2*t := by positivity
  rw [show (4:ℕ)=2*2 by decide, pow_mul, radius, Real.sq_sqrt (Real.sqrt_nonneg _),
    Real.sq_sqrt h]

theorem radius_hasDerivAt {r₀ t : ℝ} (hr : 0 < r₀) (ht : 0 ≤ t) :
    HasDerivAt (radius r₀) (1 / (2 * radius r₀ t ^ 3)) t := by
  have h : 0 < r₀^4+2*t := by positivity
  have h1 := Real.sqrt_pos_of_pos h
  have h2 := Real.sqrt_pos_of_pos h1
  have hd : HasDerivAt (fun y : ℝ => r₀^4+2*y) 2 t := by
    simpa using (((hasDerivAt_id t).const_mul 2).const_add (r₀^4))
  apply ((hd.sqrt h.ne').sqrt h1.ne').congr_deriv
  dsimp [radius]
  field_simp [h1.ne', h2.ne']
  nlinarith [Real.sq_sqrt h1.le]

/-- The material angle has period 2π, including at the initial slice. -/
def flow (r₀ : ℝ) (hr : 0 < r₀) : ForwardImmersion where
  period := 2 * Real.pi
  period_pos := Real.two_pi_pos
  position t := scalePosition (radius r₀ t) unitCircle
  periodic t _ := scalePosition_periodic _ (periodic_circleMap 0 1)
  initial_smooth := scalePosition_smooth _ (contDiff_circleMap 0 1)
  interior_joint_smooth := by
    intro z hz
    apply ContDiffAt.contDiffWithinAt
    change ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => radius r₀ z.1 • unitCircle z.2) z
    have hrad : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => radius r₀ p.1) z := by
      have h : 0 < r₀^4+2*z.1 := by have := hz.1; change 0 < z.1 at this; positivity
      exact ((contDiffAt_const.add (contDiffAt_const.mul contDiffAt_fst)).sqrt h.ne').sqrt
        (Real.sqrt_pos_of_pos h).ne'
    exact hrad.smul ((contDiff_circleMap 0 1).contDiffAt.comp z contDiffAt_snd)
  immersion t ht := scalePosition_regular (radius_pos hr ht)
    (fun _ => deriv_circleMap_ne_zero (by norm_num))
  spatial_jets_continuous j _ := by
    have hrcont : Continuous (fun z : ℝ × ℝ => radius r₀ z.1) :=
      ((continuous_const.add (continuous_const.mul continuous_fst)).sqrt).sqrt
    have hj : Continuous (iteratedDeriv j unitCircle) :=
      ContDiff.continuous_iteratedDeriv' j (contDiff_circleMap 0 1)
    simp only [scalePosition_iteratedDeriv]
    exact (hrcont.smul (hj.comp continuous_snd)).continuousOn

theorem flow_isNormalFEF (r₀ : ℝ) (hr : 0 < r₀) : (flow r₀ hr).IsNormalFEF := by
  intro t ht u
  have h := radius_pos hr ht.le
  change HasDerivAt (fun x => radius r₀ x • unitCircle u)
    (-(force (scalePosition (radius r₀ t) unitCircle) u : ℂ) *
      normal (scalePosition (radius r₀ t) unitCircle) u) t
  rw [scalePosition_force h, scalePosition_normal h, circleForce, circleNormal]
  apply ((radius_hasDerivAt hr ht.le).smul_const (unitCircle u)).congr_deriv
  simp [Complex.real_smul, div_eq_mul_inv, mul_assoc, mul_left_comm]

theorem one_turn (r₀ : ℝ) (hr : 0 < r₀) {t : ℝ} (ht : 0 ≤ t) :
    InjOn ((flow r₀ hr).position t) (Ico 0 (2*Real.pi)) := by
  intro x hx y hy he
  change (radius r₀ t : ℂ) * unitCircle x = (radius r₀ t : ℂ) * unitCircle y at he
  apply injOn_circleMap_of_abs_sub_le' (c := 0) (R := 1) (by norm_num)
    (by simp : 2*Real.pi-0 ≤ 2*Real.pi) hx hy
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (radius_pos hr ht).ne') he

theorem length_eq (r₀ : ℝ) (hr : 0 < r₀) {t : ℝ} (ht : 0 ≤ t) :
    (flow r₀ hr).length t = 2*Real.pi * radius r₀ t := by
  change materialLength (scalePosition (radius r₀ t) unitCircle) (2*Real.pi) = _
  rw [scalePosition_materialLength (radius_pos hr ht)]
  simp [materialLength, circleSpeed, mul_comm]

theorem energy_eq (r₀ : ℝ) (hr : 0 < r₀) {t : ℝ} (ht : 0 ≤ t) :
    (flow r₀ hr).energy t = Real.pi / radius r₀ t := by
  change materialEnergy (scalePosition (radius r₀ t) unitCircle) (2*Real.pi) = _
  rw [scalePosition_materialEnergy (radius_pos hr ht)]
  simp [materialEnergy, circleCurvature, circleSpeed]

theorem dissipation_eq (r₀ : ℝ) (hr : 0 < r₀) {t : ℝ} (ht : 0 ≤ t) :
    (flow r₀ hr).dissipation t = Real.pi / (2 * radius r₀ t ^ 5) := by
  change materialDissipation (scalePosition (radius r₀ t) unitCircle) (2*Real.pi) = _
  rw [scalePosition_materialDissipation (radius_pos hr ht)]
  simp [materialDissipation, circleForce, circleSpeed]
  ring

theorem fourth_length_eq (r₀ : ℝ) (hr : 0 < r₀) {t : ℝ} (ht : 0 ≤ t) :
    (flow r₀ hr).length t ^ 4 = (2*Real.pi)^4 * (r₀^4 + 2*t) := by
  rw [length_eq r₀ hr ht, mul_pow, radius_fourth hr ht]

theorem static_equalities (r₀ : ℝ) (hr : 0 < r₀) {t : ℝ} (ht : 0 ≤ t) :
    let c := flow r₀ hr
    c.energy t * c.length t = 2*Real.pi^2 ∧
      c.dissipation t / c.energy t ^ 2 = 4*Real.pi^2 / c.length t ^ 3 := by
  dsimp only
  rw [length_eq r₀ hr ht, energy_eq r₀ hr ht, dissipation_eq r₀ hr ht]
  constructor
  all_goals field_simp [(radius_pos hr ht).ne', Real.pi_ne_zero]
  all_goals ring

theorem length_ratio_tendsto (r₀ : ℝ) (hr : 0 < r₀) :
    Tendsto (fun t => (flow r₀ hr).length t / Real.sqrt (Real.sqrt t))
      atTop (𝓝 (2*Real.pi*Real.sqrt (Real.sqrt 2))) := by
  have h : Tendsto (fun t : ℝ => r₀^4/t+2) atTop (𝓝 2) := by
    simpa using (tendsto_id.const_div_atTop (r₀^4)).add_const 2
  apply (h.sqrt.sqrt.const_mul (2*Real.pi)).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  rw [length_eq r₀ hr ht.le, mul_div_assoc, radius,
    ← Real.sqrt_div (Real.sqrt_nonneg _), ← Real.sqrt_div (by positivity)]
  congr 3
  field_simp [ht.ne']

theorem sharp_coefficient_fourth : (2*Real.pi*Real.sqrt (Real.sqrt 2))^4 = 32*Real.pi^4 := by
  rw [mul_pow, show (4:ℕ)=2*2 by decide, pow_mul (Real.sqrt _),
    Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  ring

theorem length_quarter_ratio_tendsto (r₀ : ℝ) (hr : 0 < r₀) :
    Tendsto (fun t : ℝ => (flow r₀ hr).length t / t ^ (1/4:ℝ))
      atTop (𝓝 (2*Real.pi*(2:ℝ)^(1/4:ℝ))) := by
  have hroot {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) = x^(1/4:ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
    norm_num
  rw [← hroot (by norm_num : (0:ℝ) ≤ 2)]
  apply (length_ratio_tendsto r₀ hr).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  rw [hroot ht.le]

end LengthGrowth.ActualFlow.SharpCircle

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (n, _) in (← getEnv).constants do
    if (`LengthGrowth.ActualFlow.SharpCircle).isPrefixOf n then
      for a in (← collectAxioms n) do
        unless (#[`propext, `Classical.choice, `Quot.sound] : Array Name).contains a do
          throwError "Unexpected axiom {a} in {n}"
      count := count+1
  logInfo m!"SHARP_CIRCLE_AUDIT {count} declarations with standard axioms"
