import LengthGrowth.OscillatorMeanBounds
import LengthGrowth.OscillatorScalarIntegral
import Lean.Util.CollectAxioms

/-! Positive mean of the paired quartic oscillator by analytic quadrature.
Both endpoints of the parameter interval are included. -/
noncomputable section
namespace LengthGrowth.OscillatorMean
open Real Set MeasureTheory

private theorem baseline_low {y : ℝ} (hy : y^2 ≤ 1) : -(3/11:ℝ)≤baseline y := by
  apply (le_div_iff₀ (show 0<4+7*y^2 by positivity)).mpr
  linarith

private theorem baseline_cont : Continuous (fun x : ℝ => baseline (cos x)) := by
  unfold baseline
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    positivity

/-- Uniform positive lower bound for the paired angular integrand. -/
theorem angular_mean_lower {c : ℝ} (hc : 0≤c) (hcu : c≤1/2) :
    4*π/385 < ∫ θ in 0..π/2,angular c θ := by
  let f : ℝ → ℝ := fun θ => (8/7)*baseline (cos θ)
  let loss : ℝ := (8/3-8/7)*(3/11)
  have cf : Continuous f := baseline_cont.const_mul _
  have ca := continuous_angular hc hcu
  have bounds (θ : ℝ) := pointwise hc hcu
    (show (cos θ)^2≤1 by nlinarith [sin_sq_add_cos_sq θ,sq_nonneg (sin θ)])
  have lower (θ : ℝ) : f θ-loss ≤ angular c θ := by
    obtain ⟨hw,hwu,hb⟩ := bounds θ
    have ylow := baseline_low (show (cos θ)^2 ≤ 1 by
      nlinarith [sin_sq_add_cos_sq θ,sq_nonneg (sin θ)])
    have prod := mul_le_mul_of_nonneg_left hb (show 0≤weight c (cos θ) by linarith)
    dsimp [f,loss,angular]
    nlinarith only [prod,hwu,mul_nonneg (sub_nonneg.mpr hw) (sub_nonneg.mpr ylow)]
  have upperhalf (θ : ℝ) (hθ : θ∈Icc (π/4) (π/2)) : f θ ≤ angular c θ := by
    obtain ⟨hw,_,hb⟩ := bounds θ
    have cos2 := cos_le_cos_of_nonneg_of_le_pi (x:=π/2) (y:=2*θ)
      (by positivity) (by linarith [hθ.2]) (by linarith [hθ.1])
    rw [cos_two_mul,cos_pi_div_two] at cos2
    have hbn : 0≤baseline (cos θ) := div_nonneg (by linarith) (by positivity)
    exact le_trans (mul_le_mul_of_nonneg_right hw hbn)
      (mul_le_mul_of_nonneg_left hb (by linarith))
  have lo := intervalIntegral.integral_mono_on (μ:=volume) (a:=0) (b:=π/4)
    (by positivity) ((cf.sub continuous_const).intervalIntegrable 0 (π/4))
    (ca.intervalIntegrable 0 (π/4)) (fun θ _ => lower θ)
  have hi := intervalIntegral.integral_mono_on (μ:=volume) (a:=π/4) (b:=π/2)
    (by linarith [pi_pos]) (cf.intervalIntegrable _ _) (ca.intervalIntegrable _ _) upperhalf
  have ef := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (cf.intervalIntegrable 0 (π/4)) (cf.intervalIntegrable (π/4) (π/2))
  have ea := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (ca.intervalIntegrable 0 (π/4)) (ca.intervalIntegrable (π/4) (π/2))
  change (∫ θ in 0..π/4,f θ-loss) ≤ _ at lo
  rw [intervalIntegral.integral_sub (cf.intervalIntegrable 0 (π/4))
    (continuous_const.intervalIntegrable _ _),intervalIntegral.integral_const] at lo
  simp only [sub_zero,smul_eq_mul] at lo
  have val : (∫ θ in 0..π/2,f θ)=(8/7)*(π*(2/√11-1/2)) := by
    dsimp only [f,baseline]
    rw [intervalIntegral.integral_const_mul,baseline_integral_exact]
  have hr : 0<√(11:ℝ) := by positivity
  have h5 : (3/5:ℝ)<2/√11 := (lt_div_iff₀ hr).mpr (by
    nlinarith [sq_sqrt (show (0:ℝ)≤11 by norm_num)])
  have hval : π/10<π*(2/√11-1/2) := by nlinarith only [mul_pos pi_pos (sub_pos.mpr h5)]
  dsimp only [loss] at lo
  linarith only [lo,hi,ef,ea,val,hval]

/-- The substitution `θ=2 arctan u` gives precisely the radical and Jacobian
used in rational half-angle coordinates. -/
def pairedIntegrand (c u : ℝ) : ℝ :=
  let y := (1-u^2)/(1+u^2)
  (2/(1+u^2))*weight c y*factor c y

theorem paired_integral_eq_angular {c : ℝ} (hc : 0≤c) (hcu : c≤1/2) :
    (∫ u in 0..1,pairedIntegrand c u) = ∫ θ in 0..π/2,angular c θ := by
  let φ : ℝ → ℝ := fun u => 2*arctan u
  let j : ℝ → ℝ := fun u => 2/(1+u^2)
  have d (u : ℝ) : HasDerivAt φ (j u) u := by
    change HasDerivAt (fun v : ℝ => 2*arctan v) (2/(1+u^2)) u
    rw [show 2/(1+u^2)=2*(1/(1+u^2)) by ring]
    exact (hasDerivAt_arctan u).const_mul 2
  have cj : Continuous j := continuous_const.div (continuous_const.add (continuous_id.pow 2))
    (fun u => (show 0<1+u^2 by positivity).ne')
  have sub := intervalIntegral.integral_comp_mul_deriv (a:=0) (b:=1)
    (fun u _ => d u) cj.continuousOn (continuous_angular hc hcu)
  have co (u : ℝ) : cos (φ u)=(1-u^2)/(1+u^2) := by
    rw [show φ u=2*arctan u by rfl,cos_two_mul,cos_sq_arctan]
    field_simp [show (1+u^2)≠0 by positivity]
    ring
  have fun_eq : (fun u => ((angular c) ∘ φ) u*j u)=pairedIntegrand c := by
    funext u
    simp only [Function.comp_apply,angular,co,pairedIntegrand,j]
    ring
  rw [fun_eq] at sub
  simpa [φ,arctan_one,show 2*(π/4)=π/2 by ring] using sub

theorem paired_integral_lower {c : ℝ} (hc : 0≤c) (hcu : c≤1/2) :
    4*π/385 < ∫ u in 0..1,pairedIntegrand c u := by
  rw [paired_integral_eq_angular hc hcu]
  exact angular_mean_lower hc hcu

theorem paired_integral_pos {c : ℝ} (hc : 0≤c) (hcu : c≤1/2) :
    0 < ∫ u in 0..1,pairedIntegrand c u :=
  lt_trans (by positivity) (paired_integral_lower hc hcu)

end LengthGrowth.OscillatorMean

open Lean Elab Command in
run_cmd do
  for (n,_) in (← getEnv).constants do
    if (`LengthGrowth.OscillatorMean).isPrefixOf n then
      for ax in (← collectAxioms n) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains ax do
          throwError "Unexpected axiom {ax} for {n}"
  logInfo "OSCILLATOR_MEAN_AUDIT: analytic bounds, quadrature, half-angle substitution, uniform positive integral."
