import LengthGrowth.ActualFlow.ArclengthCoercivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! Bending energy counted on all visits of a closed unit-speed curve to a disk. -/
noncomputable section
open Set MeasureTheory
namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

def diskEnergy (p : ℂ) (R : ℝ) : ℝ :=
  ∫ s in 0..c.period, (c.curve ⁻¹' Metric.closedBall p R).indicator
    (fun s => c.curvature s ^ 2 / 2) s

private def weight (R x : ℝ) := (1 + (x / R)^2)⁻¹
private def potential (R x : ℝ) := R * Real.arctan (x / R)

private theorem wpos (R x : ℝ) : 0 ≤ weight R x := by unfold weight; positivity

private theorem whalf {R x : ℝ} (hR : 0 < R) (hx : |x| ≤ R) : 1/2 ≤ weight R x := by
  have hb : |x / R| ≤ 1 := by rw [abs_div,abs_of_pos hR]; exact (div_le_one hR).mpr hx
  have hsq := sq_le_sq' (abs_le.mp hb).1 (abs_le.mp hb).2
  unfold weight
  rw [← one_div]
  apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<2) (by positivity)).mpr
  nlinarith

private theorem potential_bound {R : ℝ} (hR : 0 < R) (x : ℝ) :
    |potential R x| ≤ R * Real.pi := by
  rw [potential,abs_mul,abs_of_pos hR]
  apply mul_le_mul_of_nonneg_left _ hR.le
  exact abs_le.mpr ⟨by linarith [Real.neg_pi_div_two_lt_arctan (x/R), Real.pi_pos],
    by linarith [Real.arctan_lt_pi_div_two (x/R), Real.pi_pos]⟩

private theorem pot_deriv {R : ℝ} (hR : 0 < R) (x : ℝ) :
    HasDerivAt (potential R) (weight R x) x := by
  have hd := ((Real.hasDerivAt_arctan (x/R)).comp x ((hasDerivAt_id x).div_const R)).const_mul R
  convert! hd using 1
  unfold weight
  field_simp [hR.ne']

private def axisDensity (l : ℂ →L[ℝ] ℝ) (p : ℂ) (R s : ℝ) :=
  weight R (l (c.curve s - p)) * (l (c.tangent s))^2 * c.curvature s^2

def cost (s : ℝ) := 2 * |c.curvature s| * |c.curvature₁ s| + |c.curvature s|^3

theorem cost_cont : Continuous c.cost :=
  ((c.curvature_continuous.abs.const_mul 2).mul c.curvature₁_continuous.abs).add
    (c.curvature_continuous.abs.pow 3)

private theorem curve_cont : Continuous c.curve :=
  continuous_iff_continuousAt.mpr fun s => (c.curve_deriv s).continuousAt

private theorem axis_cont (l : ℂ →L[ℝ] ℝ) (p : ℂ) (R : ℝ) :
    Continuous (c.axisDensity l p R) := by
  unfold axisDensity weight
  exact (((continuous_const.add (((l.continuous.comp (c.curve_cont.sub continuous_const)).div_const R).pow 2)).inv₀
    (fun x => (by change 1 + (l (c.curve x - p) / R)^2 ≠ 0; positivity))).mul ((l.continuous.comp c.tangent_continuous).pow 2)).mul (c.curvature_continuous.pow 2)

private theorem axis_bound (l : ℂ →L[ℝ] ℝ) (hl : ∀ z, |l z| ≤ ‖z‖)
    (p : ℂ) {R : ℝ} (hR : 0 < R) :
    (∫ s in 0..c.period, c.axisDensity l p R s) ≤ R * Real.pi * ∫ s in 0..c.period, c.cost s := by
  let f := fun s => potential R (l (c.curve s - p)) * l (c.tangent s) * c.curvature s^2
  let v := fun s => potential R (l (c.curve s - p)) *
    (l (c.normal s) * c.curvature s^3 + 2 * l (c.tangent s) * c.curvature s * c.curvature₁ s)
  have hd (s : ℝ) : HasDerivAt f (c.axisDensity l p R s + v s) s := by
    have hx := l.hasFDerivAt.comp_hasDerivAt s ((c.curve_deriv s).sub_const p)
    have ht := l.hasFDerivAt.comp_hasDerivAt s (c.tangent_deriv s)
    have ht' : HasDerivAt (fun x => l (c.tangent x)) (c.curvature s * l (c.normal s)) s := by
      simpa only [← Complex.real_smul, map_smul, smul_eq_mul, normal, Function.comp_def] using ht
    have h := (((pot_deriv hR _).comp s hx).mul ht').mul ((c.curvature_deriv s).pow 2)
    convert! h using 1
    simp [v, axisDensity, Function.comp_def]
    ring
  have hpc : Continuous (fun s => potential R (l (c.curve s-p))) :=
    (continuous_iff_continuousAt.mpr (fun x => (pot_deriv hR x).continuousAt)).comp
      (l.continuous.comp (c.curve_cont.sub continuous_const))
  have hnc : Continuous c.normal := continuous_iff_continuousAt.mpr fun s => (c.normal_deriv s).continuousAt
  have hv : Continuous v := hpc.mul (((l.continuous.comp hnc).mul (c.curvature_continuous.pow 3)).add
    (((l.continuous.comp c.tangent_continuous).const_mul 2).mul c.curvature_continuous |>.mul c.curvature₁_continuous))
  have hzero := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := c.period) (fun s _ => hd s)
    (((c.axis_cont l p R).add hv).intervalIntegrable 0 c.period)
  have hp : f c.period = f 0 := by
    dsimp [f]
    rw [show c.curve c.period = c.curve 0 by simpa using c.curve_periodic 0,
      show c.tangent c.period = c.tangent 0 by simpa using c.tangent_periodic 0,
      show c.curvature c.period = c.curvature 0 by simpa using c.curvature_periodic 0]
  rw [hp, sub_self, intervalIntegral.integral_add ((c.axis_cont l p R).intervalIntegrable _ _) (hv.intervalIntegrable _ _)] at hzero
  have hb (s : ℝ) : -v s ≤ R * Real.pi * c.cost s := by
    have ht : |l (c.tangent s)| ≤ 1 := (hl _).trans_eq (c.tangent_unit s)
    have hn : |l (c.normal s)| ≤ 1 := (hl _).trans_eq (c.normal_unit s)
    apply (neg_le_abs _).trans
    unfold v cost
    rw [abs_mul]
    apply mul_le_mul (potential_bound hR _) _ (abs_nonneg _) (mul_nonneg hR.le Real.pi_pos.le)
    apply (abs_add_le ..).trans
    simp only [abs_mul, abs_pow, show |(2:ℝ)|=2 by norm_num]
    nlinarith [mul_le_mul_of_nonneg_right hn (pow_nonneg (abs_nonneg (c.curvature s)) 3),
      mul_le_mul_of_nonneg_right ht (mul_nonneg (abs_nonneg (c.curvature s)) (abs_nonneg (c.curvature₁ s)))]
  have hh : (∫ s in 0..c.period, -v s) ≤ ∫ s in 0..c.period, (R*Real.pi) * c.cost s := intervalIntegral.integral_mono_on c.period_pos.le (hv.neg.intervalIntegrable 0 c.period)
    ((c.cost_cont.const_mul (R*Real.pi)).intervalIntegrable 0 c.period) (fun s _ => hb s)
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hh
  linarith

theorem diskEnergy_le_cost (p : ℂ) {R : ℝ} (hR : 0<R) :
    c.diskEnergy p R ≤ 2 * (R * Real.pi) * ∫ s in 0..c.period, c.cost s := by
  let a := c.axisDensity Complex.reCLM p R
  let b := c.axisDensity Complex.imCLM p R
  have ha := c.axis_cont Complex.reCLM p R
  have hb := c.axis_cont Complex.imCLM p R
  have hs : MeasurableSet (c.curve ⁻¹' Metric.closedBall p R) :=
    Metric.isClosed_closedBall.measurableSet.preimage c.curve_cont.measurable
  have hi : IntervalIntegrable ((c.curve ⁻¹' Metric.closedBall p R).indicator (fun s => c.curvature s^2 / 2)) volume 0 c.period :=
    intervalIntegrable_iff.mpr ((intervalIntegrable_iff.mp (((c.curvature_continuous.pow 2).div_const 2).intervalIntegrable 0 c.period)).indicator hs)
  have hm : c.diskEnergy p R ≤ ∫ s in 0..c.period, a s + b s := by
    apply intervalIntegral.integral_mono_on c.period_pos.le hi ((ha.add hb).intervalIntegrable _ _)
    intro s _
    dsimp [a,b,axisDensity]
    by_cases hx : s ∈ c.curve ⁻¹' Metric.closedBall p R
    · rw [indicator_of_mem hx]
      have hx' : ‖c.curve s - p‖ ≤ R := by simpa only [mem_preimage, Metric.mem_closedBall, dist_eq_norm] using hx
      have h1 := whalf hR ((Complex.abs_re_le_norm _).trans hx')
      have h2 := whalf hR ((Complex.abs_im_le_norm _).trans hx')
      simp only [Complex.sub_re, Complex.sub_im] at h1 h2
      have hu := Complex.normSq_eq_norm_sq (c.tangent s)
      rw [c.tangent_unit,Complex.normSq_apply] at hu
      nlinarith [mul_le_mul_of_nonneg_right h1 (mul_nonneg (sq_nonneg (c.tangent s).re) (sq_nonneg (c.curvature s))),
        mul_le_mul_of_nonneg_right h2 (mul_nonneg (sq_nonneg (c.tangent s).im) (sq_nonneg (c.curvature s))),
        congrArg (fun x : ℝ => x*c.curvature s^2) hu]
    · rw [indicator_of_notMem hx]
      exact add_nonneg (mul_nonneg (mul_nonneg (wpos _ _) (sq_nonneg _)) (sq_nonneg _)) (mul_nonneg (mul_nonneg (wpos _ _) (sq_nonneg _)) (sq_nonneg _))
  rw [intervalIntegral.integral_add (ha.intervalIntegrable _ _) (hb.intervalIntegrable _ _)] at hm
  have h1 := c.axis_bound Complex.reCLM Complex.abs_re_le_norm p hR
  have h2 := c.axis_bound Complex.imCLM Complex.abs_im_le_norm p hR
  change c.diskEnergy p R ≤ (∫ s in 0..c.period, c.axisDensity Complex.reCLM p R s) + ∫ s in 0..c.period, c.axisDensity Complex.imCLM p R s at hm
  linarith

theorem diskEnergy_eq_energy_of_period_le {R : ℝ} (hR : c.period ≤ R) :
    c.diskEnergy (c.curve 0) R = c.energy := by
  unfold diskEnergy energy
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le c.period_pos.le] at hs
  apply indicator_of_mem
  change dist (c.curve s) (c.curve 0) ≤ R
  rw [dist_eq_norm]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => c.curve_deriv u)
    (c.tangent_continuous.intervalIntegrable 0 s)
  rw [← hi]
  calc
    _ ≤ ∫ u in 0..s, ‖c.tangent u‖ := intervalIntegral.norm_integral_le_integral_norm hs.1
    _ = s := by simp [c.tangent_unit]
    _ ≤ R := hs.2.trans hR

end LengthGrowth.ClosedFrenetCurve
