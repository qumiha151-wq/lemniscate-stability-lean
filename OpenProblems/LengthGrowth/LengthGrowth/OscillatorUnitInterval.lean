import LengthGrowth.IntervalOscillation
import LengthGrowth.OscillatorOrbitBounds
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Explicit pointwise bounds from one interval of squared curvature and
the squared residual of the tilted quartic oscillator. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace LengthGrowth.OscillatorLocal

def residual (u : ℝ → ℝ) (s : ℝ) :=
  deriv (deriv u) s + u s ^ 3 / 2 - u s / 4 - 1 / 4

def unitDensity (u : ℝ → ℝ) (s : ℝ) := u s^2+residual u s^2

private theorem density_cont {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) :
    Continuous (unitDensity u) := by
  have hd := (contDiff_infty_iff_deriv.mp hu).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  unfold unitDensity residual
  fun_prop (disch := first | exact hu.continuous | exact hdd.continuous)

private theorem density_lower {u : ℝ → ℝ} {x M a b C : ℝ} (hu : ContDiff ℝ ∞ u)
    (hM : (∫ t in x..x+1, unitDensity u t) ≤ M)
    (hx : x ≤ a) (hab : a ≤ b) (hb : b ≤ x+1)
    (hC : ∀ t ∈ Icc a b, C ≤ unitDensity u t) : (b-a)*C ≤ M := by
  have hc := density_cont hu
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    (continuous_const.intervalIntegrable a b) (hc.intervalIntegrable a b) hC
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  exact (hi.trans (intervalIntegral.integral_mono_interval hx hab hb
    (Filter.Eventually.of_forall (fun t => add_nonneg (sq_nonneg (u t)) (sq_nonneg (residual u t))))
    (hc.intervalIntegrable x (x+1)))).trans hM

private theorem end_quarter {u : ℝ → ℝ} {x M a : ℝ} (hu : ContDiff ℝ ∞ u)
    (hM : (∫ t in x..x+1, unitDensity u t) ≤ M) (h1 : 1 ≤ M)
    (hx : x ≤ a) (ha : a+1/4 ≤ x+1) :
    ∃ s ∈ Icc a (a+1/4), |u s| ≤ 2*M := by
  have hab : a ≤ a+1/4 := by linarith
  obtain ⟨s,hs,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab)
    ((hu.continuous.pow 2).continuousOn)
  have bound := density_lower hu hM hx hab ha (C := u s^2) (by
    intro t ht
    exact (hmin ht).trans (le_add_of_nonneg_right (sq_nonneg (residual u t))))
  refine ⟨s,hs,?_⟩
  nlinarith only [bound, sq_abs (u s), abs_nonneg (u s), h1,
    mul_nonneg (sub_nonneg.mpr h1) (show 0 ≤ M by linarith),
    sq_nonneg (|u s|-2*M)]

private theorem slope_anchor {u : ℝ → ℝ} {x M : ℝ} (hu : ContDiff ℝ ∞ u)
    (hM : (∫ t in x..x+1, unitDensity u t) ≤ M) (h1 : 1 ≤ M) :
    ∃ s ∈ Icc x (x+1), |deriv u s| ≤ 8*M := by
  obtain ⟨a,ha,ha'⟩ := end_quarter (a := x) hu hM h1 le_rfl (by linarith)
  obtain ⟨b,hb,hb'⟩ := end_quarter (a := x+3/4) hu hM h1 (by linarith) (by linarith)
  have hab : a < b := by linarith [ha.2,hb.1]
  obtain ⟨s,hs,hs'⟩ := exists_deriv_eq_slope u hab hu.continuous.continuousOn
    ((hu.differentiable (by simp)).differentiableOn)
  refine ⟨s,⟨by linarith [ha.1,hs.1], by linarith [hb.2,hs.2]⟩,?_⟩
  rw [hs',abs_div,abs_of_pos (sub_pos.mpr hab), div_le_iff₀ (sub_pos.mpr hab)]
  have hh : 1/2 ≤ b-a := by linarith [ha.2,hb.1]
  have hn := abs_sub (u b) (u a)
  nlinarith only [hn,ha',hb',mul_nonneg (sub_nonneg.mpr hh) (show 0 ≤ M by linarith)]

private theorem second_deriv_pointwise {y z B : ℝ} (hy : |y| ≤ B) :
    |z-y^3/2+y/4+1/4| ≤ (B/2+1/2)*(y^2+z^2)+7/8 := by
  have htr := (abs_add_le (z-y^3/2+y/4) (1/4)).trans
    (add_le_add_left (abs_add_le (z-y^3/2) (y/4)) _)
  have hsub := abs_sub z (y^3/2)
  have hy3 : |y^3/2| = |y| * (y^2)/2 := by
    rw [abs_div,abs_pow,abs_of_pos (by norm_num : (0:ℝ)<2)]
    rw [pow_succ, sq_abs]
    ring
  rw [hy3] at hsub
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<4),abs_of_pos (by norm_num : (0:ℝ)<1/4)] at htr
  have hz := sq_nonneg (|z|-1)
  have hyy := sq_nonneg (|y|-1)
  nlinarith only [htr,hsub,hz,hyy,sq_abs z,sq_abs y,sq_nonneg y,
    mul_nonneg (sub_nonneg.mpr hy) (sq_nonneg y),
    mul_nonneg ((abs_nonneg y).trans hy) (sq_nonneg z)]

private theorem slope_bound {u : ℝ → ℝ} {x M B : ℝ} (hu : ContDiff ℝ ∞ u)
    (hM : (∫ t in x..x+1, unitDensity u t) ≤ M) (h1 : 1 ≤ M)
    (hB : 0 ≤ B) (hmax : ∀ y ∈ Icc x (x+1), |u y| ≤ B) :
    ∀ y ∈ Icc x (x+1), |deriv u y| ≤ 8*M+(B/2+1/2)*M+7/8 := by
  have hd := (contDiff_infty_iff_deriv.mp hu).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  have hc := density_cont hu
  obtain ⟨s,hs,hsv⟩ := slope_anchor hu hM h1
  have hi : (∫ t in x..x+1, |deriv (deriv u) t|) ≤ (B/2+1/2)*M+7/8 := by
    have hh := intervalIntegral.integral_mono_on (μ := volume) (show x ≤ x+1 by linarith)
      (hdd.continuous.abs.intervalIntegrable x (x+1))
      (((hc.const_mul (B/2+1/2)).add continuous_const).intervalIntegrable x (x+1))
      (g := fun t => (B/2+1/2)*unitDensity u t+7/8) (by
        intro t ht
        have H := second_deriv_pointwise (z := residual u t) (hmax t ht)
        have eqn : residual u t - u t^3/2 + u t/4 + 1/4 = deriv (deriv u) t := by
          unfold residual; ring
        rw [eqn] at H
        exact H)
    rw [intervalIntegral.integral_add ((hc.const_mul _).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _),intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const,smul_eq_mul] at hh
    nlinarith only [hh,mul_le_mul_of_nonneg_left hM (by linarith : 0≤B/2+1/2)]
  intro y hy
  have hd' := hd.differentiable (by simp)
  have osc := LengthGrowth.interval_oscillation_le (fun t => (hd' t).hasDerivAt)
    hdd.continuous hy hs
  simp only [Real.norm_eq_abs] at osc
  have tri : |deriv u y| ≤ |deriv u y-deriv u s|+|deriv u s| := by
    calc
      _ = |deriv u y-deriv u s+deriv u s| := by rw [sub_add_cancel]
      _ ≤ _ := abs_add_le _ _
  linarith

/-- Simultaneous position and slope bounds throughout the unit interval
from the single integral of the actual residual and position. -/
theorem unit_interval_data {u : ℝ → ℝ} {x M : ℝ} (hu : ContDiff ℝ ∞ u)
    (h1 : 1 ≤ M) (hM : (∫ t in x..x+1, unitDensity u t) ≤ M)
    (y : ℝ) (hy : y ∈ Icc x (x+1)) : |u y| ≤ 10*M ∧ |deriv u y| ≤ 16*M^2 := by
  have h0 : 0 < M := by linarith
  obtain ⟨p,hp,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (by linarith : x ≤ x+1)) hu.continuous.abs.continuousOn
  let B := |u p|
  have hB : 0 ≤ B := abs_nonneg _
  have hmax' : ∀ t ∈ Icc x (x+1), |u t| ≤ B := fun _ ht => hmax ht
  have hs := slope_bound hu hM h1 hB hmax'
  have bound : B ≤ 10*M := by
    by_cases hsmall : B < 1
    · linarith
    have hbig : 1 ≤ B := le_of_not_gt hsmall
    have hs' (t : ℝ) (ht : t ∈ Icc x (x+1)) : ‖deriv u t‖ ≤ 12*M*B := by
      rw [Real.norm_eq_abs]
      nlinarith only [hs t ht,h1,mul_nonneg h0.le (sub_nonneg.mpr hbig)]
    let d := 1/(24*M)
    have hd : 0 < d := by dsimp [d]; positivity
    have hdm : d*(24*M)=1 := by dsimp [d]; field_simp
    have hdhalf : d ≤ 1/2 := by
      dsimp [d]
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    obtain ⟨a,ha,hap,hap',hab⟩ : ∃ a, x ≤ a ∧ a ≤ p ∧ p ≤ a+d ∧ a+d ≤ x+1 := by
      by_cases h : p+d ≤ x+1
      · exact ⟨p,hp.1,le_rfl,by linarith,h⟩
      · exact ⟨p-d,by linarith,by linarith,by linarith,by linarith [hp.2]⟩
    have hlower (t : ℝ) (ht : t ∈ Icc a (a+d)) : B^2/4 ≤ unitDensity u t := by
      have ht' : t ∈ Icc x (x+1) := ⟨ha.trans ht.1,ht.2.trans hab⟩
      have hh := Convex.norm_image_sub_le_of_norm_deriv_le
        (fun t _ => hu.differentiable (by simp) t) hs' (convex_Icc x (x+1)) ht' hp
      simp only [Real.norm_eq_abs] at hh
      have dt : |p-t| ≤ d := abs_le.mpr ⟨by linarith [ht.2],by linarith [ht.1]⟩
      have tr : B ≤ |u p-u t|+|u t| := by
        dsimp only [B]
        calc
          _ = |u p-u t+u t| := by rw [sub_add_cancel]
          _ ≤ _ := abs_add_le _ _
      have mulid : 12*M*B*d=B/2 := by linear_combination (B/2)*hdm
      have half : B/2 ≤ |u t| := by
        linarith [mul_le_mul_of_nonneg_left dt (show 0 ≤ 12*M*B by positivity)]
      have sq := mul_self_le_mul_self (by linarith : 0≤B/2) half
      dsimp only [unitDensity]
      nlinarith only [sq,sq_abs (u t),sq_nonneg (residual u t)]
    have hi := density_lower hu hM ha (show a ≤ a+d by linarith) hab hlower
    have scaled := mul_le_mul_of_nonneg_left hi (show 0≤24*M by positivity)
    have hsq : B^2 ≤ 96*M^2 := by
      linear_combination 4*scaled - B^2 * hdm
    by_contra! bad
    have hh := mul_pos (sub_pos.mpr bad) (show 0 < B+10*M by positivity)
    nlinarith only [hsq,hh,sq_nonneg M]
  refine ⟨(hmax' y hy).trans bound,?_⟩
  nlinarith only [hs y hy,mul_le_mul_of_nonneg_right bound h0.le,h1,
    mul_nonneg (sub_nonneg.mpr h1) h0.le]

/-- Any exact oscillator initialized with the actual value and derivative
at the beginning of a controlled interval obeys the stated global bounds.
Its initial time `a` can differ from the base point `x` of the periodic input. -/
theorem exact_orbit_from_unit_interval {u z : ℝ → ℝ} {x a M : ℝ}
    (hu : ContDiff ℝ ∞ u) (hM : 1≤M) (hi : (∫ s in x..x+1, unitDensity u s) ≤ M)
    (hz : ContDiff ℝ ∞ z) (ode : ∀ t, deriv (deriv z) t = -(z t)^3/2+z t/4+1/4)
    (hpos : z a=u x) (hspeed : deriv z a=deriv u x) (t : ℝ) :
    oscillatorEnergy z t ≤ 1400*M^4 ∧ |z t| ≤ 20*M ∧ |deriv z t| ≤ 60*M^2 := by
  have h := unit_interval_data hu hM hi x ⟨le_rfl,by linarith⟩
  exact oscillator_orbit_data hz ode hM (hpos ▸ h.1) (hspeed ▸ h.2) t

#print axioms unit_interval_data
#print axioms exact_orbit_from_unit_interval
end LengthGrowth.OscillatorLocal
