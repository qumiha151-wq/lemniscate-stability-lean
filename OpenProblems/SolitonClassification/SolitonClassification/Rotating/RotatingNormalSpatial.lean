import SolitonClassification.Rotating.RotatingNormalEvolutionContinuity
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Actual initial-value differentiability for the constructed periodic scalar flow,
including stationary trajectories. The proof uses the global Lipschitz estimate
derived from periodicity. Proof strategy adapted from the independently built
OpenTranslator scalar-flow development; no other problem project is imported. -/
namespace SolitonClassification.Rotating.NormalEvolution
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

variable (g : PeriodicScalarField)

def scalarTrajectorySlope (x y t : ℝ) : ℝ :=
  slope (g) (scalarFlow g t x) (scalarFlow g t y)

theorem scalarTrajectorySlope_continuous {x y : ℝ} (hxy : y≠x) :
    Continuous (scalarTrajectorySlope g x y) := by
  unfold scalarTrajectorySlope
  simp only [slope_def_field]
  apply ((g.smooth.continuous.comp (scalarFlow_time_smooth g y).continuous).sub
    (g.smooth.continuous.comp (scalarFlow_time_smooth g x).continuous)).div
    ((scalarFlow_time_smooth g y).continuous.sub (scalarFlow_time_smooth g x).continuous)
  intro t
  exact sub_ne_zero.mpr (fun he => hxy ((scalarFlow_bijective g t).1 he))

theorem scalarFlow_difference {x y : ℝ} (hxy : y≠x) (t : ℝ) :
    scalarFlow g t y-scalarFlow g t x =
      (y-x)*Real.exp (∫ r in 0..t, scalarTrajectorySlope g x y r) := by
  let A := scalarTrajectorySlope g x y
  have hAc : Continuous A := scalarTrajectorySlope_continuous g hxy
  let I := fun t => ∫ r in 0..t, A r
  have hI : ∀ t, HasDerivAt I (A t) t :=
    fun t => (hAc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hd : ∀ r, HasDerivAt (fun s => scalarFlow g s y-scalarFlow g s x)
      (A r*(scalarFlow g r y-scalarFlow g r x)) r := by
    intro r
    have he : A r*(scalarFlow g r y-scalarFlow g r x)=
        g (scalarFlow g r y)-g (scalarFlow g r x) := by
      simpa only [A,scalarTrajectorySlope,smul_eq_mul,mul_comm,vsub_eq_sub] using
        sub_smul_slope (g) (scalarFlow g r x) (scalarFlow g r y)
    rw [he]
    exact (scalarFlow_hasDerivAt g y r).sub (scalarFlow_hasDerivAt g x r)
  let W := fun r => (scalarFlow g r y-scalarFlow g r x)*Real.exp (-I r)
  have hW : ∀ r, HasDerivAt W 0 r := by
    intro r
    convert (hd r).mul (hI r).neg.exp using 1 <;> first | rfl | ring
  have hc := is_const_of_deriv_eq_zero
    (fun r => (hW r).differentiableAt) (fun r => (hW r).deriv) t 0
  have he : (scalarFlow g t y-scalarFlow g t x)*Real.exp (-I t)=y-x := by
    simpa only [W,I,scalarFlow_zero,intervalIntegral.integral_same,neg_zero,Real.exp_zero,mul_one] using hc
  have hm := congrArg (fun v => v*Real.exp (I t)) he
  simpa only [mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one] using hm

theorem scalarFlow_slope {x y : ℝ} (hxy : y≠x) (t : ℝ) :
    slope (scalarFlow g t) x y =
      Real.exp (∫ r in 0..t, scalarTrajectorySlope g x y r) := by
  rw [slope_def_field,scalarFlow_difference g hxy t,
    mul_div_cancel_left₀ _ (sub_ne_zero.mpr hxy)]

theorem scalarTrajectorySlope_tendsto (x r : ℝ) :
    Tendsto (fun y => scalarTrajectorySlope g x y r) (𝓝[≠] x)
      (𝓝 (deriv (g) (scalarFlow g r x))) := by
  have hn : Tendsto (scalarFlow g r) (𝓝[≠] x) (𝓝[≠] scalarFlow g r x) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(scalarFlow_space_continuous g r).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact fun he => hy ((scalarFlow_bijective g r).1 he)
  exact (hasDerivAt_iff_tendsto_slope.mp
    (g.smooth.differentiable (by simp) _).hasDerivAt).comp hn

theorem scalarTrajectorySlope_bound (x y r : ℝ) :
    ‖scalarTrajectorySlope g x y r‖ ≤ scalarLip g := by
  have hh := lipschitzWith_iff_norm_sub_le.mp (scalarField_lipschitz g)
    (scalarFlow g r y) (scalarFlow g r x)
  rw [scalarTrajectorySlope,slope_def_field,norm_div]
  by_cases he : scalarFlow g r y=scalarFlow g r x
  · simp only [he,sub_self,norm_zero,zero_div]
    exact (scalarLip g).coe_nonneg
  · exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr he))).mpr hh

theorem scalarTrajectorySlope_integral_tendsto (x t : ℝ) :
    Tendsto (fun y => ∫ r in 0..t, scalarTrajectorySlope g x y r) (𝓝[≠] x)
      (𝓝 (∫ r in 0..t, deriv (g) (scalarFlow g r x))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (scalarLip g : ℝ))
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact (scalarTrajectorySlope_continuous g hy).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y =>
      Filter.Eventually.of_forall fun r _ => scalarTrajectorySlope_bound g x y r
  · exact intervalIntegrable_const
  · filter_upwards with r _
    exact scalarTrajectorySlope_tendsto g x r

def scalarJacobian (t x : ℝ) : ℝ :=
  Real.exp (∫ r in 0..t, deriv (g) (scalarFlow g r x))

theorem scalarFlow_hasDerivAt_initial (t x : ℝ) :
    HasDerivAt (scalarFlow g t) (scalarJacobian g t x) x := by
  rw [hasDerivAt_iff_tendsto_slope]
  have h := (Real.continuous_exp.tendsto _).comp (scalarTrajectorySlope_integral_tendsto g x t)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (scalarFlow_slope g hy t).symm

theorem scalarJacobian_pos (t x : ℝ) : 0<scalarJacobian g t x := Real.exp_pos _

theorem scalarFlow_spatial_derivative_pos (t x : ℝ) : 0<deriv (scalarFlow g t) x := by
  rw [(scalarFlow_hasDerivAt_initial g t x).deriv]
  exact scalarJacobian_pos g t x

end
end SolitonClassification.Rotating.NormalEvolution

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Periodic scalar spatial audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Periodic scalar spatial audit passed for {count} declarations."
