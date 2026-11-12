import LengthGrowth.StressDirectionBounds

/-! Quantitative use of actual geometric closure in the stress proof. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate
namespace LengthGrowth.ClosedFrenetCurve

variable (c : LengthGrowth.ClosedFrenetCurve)

theorem invertedStress_eq_direction (s : ℝ) (hs : c.stress s ≠ 0) :
    c.invertedStress s = ((‖c.stress s‖⁻¹ : ℝ) : ℂ)*c.stressDirection s := by
  have hn : (‖c.stress s‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hs)
  dsimp [invertedStress, stressDirection]
  rw [Complex.inv_def]
  simp only [Complex.conj_conj, Complex.normSq_eq_norm_sq,
    Complex.norm_conj, Complex.ofReal_inv, Complex.ofReal_pow]
  field_simp [hn]

theorem unit_projection_lower {v z : ℂ} (hv : ‖v‖ = 1)
    (hd : ‖z-v‖ ≤ (1:ℝ)/2) : (1:ℝ)/2 ≤ (conj v*z).re := by
  have hn := Complex.abs_re_le_norm (conj v*(z-v))
  rw [norm_mul, Complex.norm_conj, hv, one_mul] at hn
  have hs : (conj v*v).re = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_eq_norm_sq, hv]
  rw [mul_sub, Complex.sub_re, hs] at hn
  have hl := neg_le_abs ((conj v*z).re-1)
  linarith

theorem stress_integral_lower_bound {M : ℝ} (_hM : 0 < M) {v : ℂ}
    (hv : ‖v‖ = 1) (hW : ∀ s, c.stress s ≠ 0)
    (hupper : ∀ s ∈ Icc 0 c.period, ‖c.stress s‖ ≤ M^2)
    (hcone : ∀ s ∈ Icc 0 c.period,
      (1:ℝ)/2 ≤ (conj v*c.stressDirection s).re) :
    c.energy/(2*M^2) ≤
      ‖∫ s in 0..c.period, ((c.curvature s : ℂ)^2/2)*c.invertedStress s‖ := by
  let a : ℝ → ℂ := fun s => ((c.curvature s : ℂ)^2/2)*c.invertedStress s
  have ha : Continuous a :=
    (((Complex.continuous_ofReal.comp c.curvature_continuous).pow 2).div_const 2).mul
      (c.invertedStress_continuous hW)
  have hp (s : ℝ) (hs : s ∈ Icc 0 c.period) :
      c.curvature s^2/(4*M^2) ≤ (conj v*a s).re := by
    have hw : 0 < ‖c.stress s‖ := norm_pos_iff.mpr (hW s)
    have heq : (conj v*a s).re =
        (c.curvature s^2/(2*‖c.stress s‖))*(conj v*c.stressDirection s).re := by
      dsimp [a]
      rw [c.invertedStress_eq_direction s (hW s)]
      simp only [Complex.ofReal_inv]
      rw [show conj v * (((c.curvature s : ℂ)^2/2) *
          ((‖c.stress s‖ : ℂ)⁻¹*c.stressDirection s)) =
          ((c.curvature s^2/(2*‖c.stress s‖) : ℝ) : ℂ)*
            (conj v*c.stressDirection s) by
        simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
          Complex.ofReal_ofNat]
        ring]
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [heq]
    calc
      _ ≤ c.curvature s^2/(4*‖c.stress s‖) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          (mul_le_mul_of_nonneg_left (hupper s hs) (by norm_num))
      _ = (c.curvature s^2/(2*‖c.stress s‖))*((1:ℝ)/2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcone s hs) (by positivity)
  have hint := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun s => c.curvature s^2/(4*M^2))
    (g := fun s => (conj v*a s).re) c.period_pos.le
    (((c.curvature_continuous.pow 2).div_const (4*M^2)).intervalIntegrable _ _)
    ((Complex.continuous_re.comp (continuous_const.mul ha)).intervalIntegrable _ _) hp
  have hleft : (∫ s in 0..c.period, c.curvature s^2/(4*M^2)) =
      c.energy/(2*M^2) := by
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_mul_const]
    dsimp [energy]
    ring
  have hright := Complex.reCLM.intervalIntegral_comp_comm
    (μ := volume) (f := fun s => conj v*a s)
    ((continuous_const.mul ha).intervalIntegrable 0 c.period)
  change (∫ s in 0..c.period, (conj v*a s).re) =
    (∫ s in 0..c.period, conj v*a s).re at hright
  rw [intervalIntegral.integral_const_mul] at hright
  rw [hleft, hright] at hint
  have hn := Complex.re_le_norm (conj v*(∫ s in 0..c.period, a s))
  rw [norm_mul, Complex.norm_conj, hv, one_mul] at hn
  exact hint.trans hn

theorem stress_integral_upper_bound {M : ℝ} (hM : 0 < M)
    (hlower : ∀ s, M^2/4 ≤ ‖c.stress s‖) :
    ‖∫ s in 0..c.period, ((c.curvature s : ℂ)^2/2)*c.invertedStress s‖ ≤
      16*Real.sqrt (2*c.energy*c.dissipation)/M^4 := by
  have hW : ∀ s, c.stress s ≠ 0 := by
    intro s
    apply norm_pos_iff.mp
    exact lt_of_lt_of_le (by positivity : 0 < M^2/4) (hlower s)
  rw [c.closed_stress_integral hW, norm_neg]
  have hp (s : ℝ) :
      ‖(c.curvature s : ℂ)*(Complex.I*c.invertedStressDerivative s)‖ ≤
        (16/M^4)*|c.curvature s*c.force s| := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      one_mul, c.invertedStressDerivative_norm]
    rw [← mul_div_assoc]
    have hw : (M^2/4)^2 ≤ ‖c.stress s‖^2 :=
      (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr (hlower s)
    calc
      _ ≤ (|c.curvature s| * |c.force s|)/(M^2/4)^2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hw
      _ = _ := by rw [abs_mul]; field_simp; ring
  calc
    _ ≤ ∫ s in 0..c.period,
        ‖(c.curvature s : ℂ)*(Complex.I*c.invertedStressDerivative s)‖ :=
      intervalIntegral.norm_integral_le_integral_norm c.period_pos.le
    _ ≤ ∫ s in 0..c.period, (16/M^4)*|c.curvature s*c.force s| := by
      apply intervalIntegral.integral_mono_on c.period_pos.le
        ((((Complex.continuous_ofReal.comp c.curvature_continuous).mul
          (continuous_const.mul (c.invertedStressDerivative_continuous hW))).norm).intervalIntegrable _ _)
        ((((c.curvature_continuous.mul c.force_continuous).abs).const_mul
          (16/M^4)).intervalIntegrable _ _)
      intro s _
      exact hp s
    _ = (16/M^4)*(∫ s in 0..c.period, |c.curvature s*c.force s|) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (16/M^4)*Real.sqrt (2*c.energy*c.dissipation) :=
      mul_le_mul_of_nonneg_left c.absolute_curvature_force_integral_bound (by positivity)
    _ = _ := by ring

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
  logInfo m!"LengthGrowth stress-closure bounds audit passed for {checked} declarations."
