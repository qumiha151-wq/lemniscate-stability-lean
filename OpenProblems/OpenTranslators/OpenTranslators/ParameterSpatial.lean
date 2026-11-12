import OpenTranslators.ParameterFlow
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Actual initial-value differentiability, including stationary parameter
trajectories. Only local compact bounds are used for the unbounded derivative
of the original field; no global Lipschitz assumption is imposed on it. -/
namespace OpenTranslator.TranslatorParameter
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

variable {z : ℝ → TranslatorState}
variable (hz : ∀ s, HasDerivAt z (translatorNumerator (z s)) s)

theorem parameterFlow_joint_continuous :
    Continuous (fun p : ℝ × ℝ => parameterFlow hz p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hl : Tendsto (fun q : ℝ × ℝ => dist q.1 p.1+
      dist (parameterFlow hz p.1 q.2) (parameterFlow hz p.1 p.2)) (𝓝 p) (𝓝 0) := by
    have hc : Continuous (fun q : ℝ × ℝ => dist q.1 p.1+
        dist (parameterFlow hz p.1 q.2) (parameterFlow hz p.1 p.2)) :=
      (continuous_fst.dist continuous_const).add
        (((parameterFlow_space_continuous hz p.1).comp continuous_snd).dist continuous_const)
    simpa [ContinuousAt] using hc.continuousAt (x := p)
  have hb : ∀ q : ℝ × ℝ,
      dist (parameterFlow hz q.1 q.2) (parameterFlow hz p.1 p.2) ≤
      dist q.1 p.1+dist (parameterFlow hz p.1 q.2) (parameterFlow hz p.1 p.2) := by
    intro q
    apply (dist_triangle _ (parameterFlow hz p.1 q.2) _).trans
    apply add_le_add _ le_rfl
    simpa only [Real.dist_eq] using parameterFlow_time_distance hz q.2 p.1 q.1
  exact squeeze_zero (fun _ => dist_nonneg) hb hl

def parameterTrajectorySlope (x y t : ℝ) : ℝ :=
  slope (parameterField z) (parameterFlow hz t x) (parameterFlow hz t y)

theorem parameterTrajectorySlope_continuous {x y : ℝ} (hxy : y≠x) :
    Continuous (parameterTrajectorySlope hz x y) := by
  unfold parameterTrajectorySlope
  simp only [slope_def_field]
  apply (((parameterField_smooth hz).continuous.comp (parameterFlow_time_smooth hz y).continuous).sub
    ((parameterField_smooth hz).continuous.comp (parameterFlow_time_smooth hz x).continuous)).div
    ((parameterFlow_time_smooth hz y).continuous.sub (parameterFlow_time_smooth hz x).continuous)
  intro t
  exact sub_ne_zero.mpr (fun he => hxy ((parameterFlow_bijective hz t).1 he))

theorem parameterFlow_difference {x y : ℝ} (hxy : y≠x) (t : ℝ) :
    parameterFlow hz t y-parameterFlow hz t x =
      (y-x)*Real.exp (∫ r in 0..t, parameterTrajectorySlope hz x y r) := by
  let A := parameterTrajectorySlope hz x y
  have hAc : Continuous A := parameterTrajectorySlope_continuous hz hxy
  let I := fun t => ∫ r in 0..t, A r
  have hI : ∀ t, HasDerivAt I (A t) t :=
    fun t => (hAc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hd : ∀ r, HasDerivAt (fun s => parameterFlow hz s y-parameterFlow hz s x)
      (A r*(parameterFlow hz r y-parameterFlow hz r x)) r := by
    intro r
    have he : A r*(parameterFlow hz r y-parameterFlow hz r x)=
        parameterField z (parameterFlow hz r y)-parameterField z (parameterFlow hz r x) := by
      simpa only [A,parameterTrajectorySlope,smul_eq_mul,mul_comm,vsub_eq_sub] using
        sub_smul_slope (parameterField z) (parameterFlow hz r x) (parameterFlow hz r y)
    rw [he]
    exact (parameterFlow_derivative hz y r).sub (parameterFlow_derivative hz x r)
  let W := fun r => (parameterFlow hz r y-parameterFlow hz r x)*Real.exp (-I r)
  have hW : ∀ r, HasDerivAt W 0 r := by
    intro r
    convert (hd r).mul (hI r).neg.exp using 1 <;> first | rfl | ring
  have hc := is_const_of_deriv_eq_zero
    (fun r => (hW r).differentiableAt) (fun r => (hW r).deriv) t 0
  have he : (parameterFlow hz t y-parameterFlow hz t x)*Real.exp (-I t)=y-x := by
    simpa only [W,I,parameterFlow_zero,intervalIntegral.integral_same,neg_zero,Real.exp_zero,mul_one] using hc
  have hm := congrArg (fun v => v*Real.exp (I t)) he
  simpa only [mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one] using hm

theorem parameterFlow_slope {x y : ℝ} (hxy : y≠x) (t : ℝ) :
    slope (parameterFlow hz t) x y =
      Real.exp (∫ r in 0..t, parameterTrajectorySlope hz x y r) := by
  rw [slope_def_field,parameterFlow_difference hz hxy t,
    mul_div_cancel_left₀ _ (sub_ne_zero.mpr hxy)]

theorem parameterTrajectorySlope_tendsto (x r : ℝ) :
    Tendsto (fun y => parameterTrajectorySlope hz x y r) (𝓝[≠] x)
      (𝓝 (deriv (parameterField z) (parameterFlow hz r x))) := by
  have hn : Tendsto (parameterFlow hz r) (𝓝[≠] x) (𝓝[≠] parameterFlow hz r x) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(parameterFlow_space_continuous hz r).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact fun he => hy ((parameterFlow_bijective hz r).1 he)
  exact (hasDerivAt_iff_tendsto_slope.mp
    ((parameterField_smooth hz).differentiable (by simp) _).hasDerivAt).comp hn

theorem parameterFlow_mem_compact_window {x y r t : ℝ}
    (hy : y∈Ioo (x-1) (x+1)) (hr : r∈uIcc 0 t) :
    parameterFlow hz r y ∈ Icc (x-1-|t|) (x+1+|t|) := by
  have hrlo : -|t|≤r := (le_min (by linarith [abs_nonneg t]) (neg_abs_le t)).trans hr.1
  have hrhi : r≤|t| := hr.2.trans (max_le (abs_nonneg t) (le_abs_self t))
  have hrt : |r|≤|t| := abs_le.mpr ⟨hrlo,hrhi⟩
  have hd := abs_le.mp (parameterFlow_displacement hz y r)
  constructor <;> linarith [hy.1,hy.2,hd.1,hd.2]

theorem parameterTrajectorySlope_local_bound (x t : ℝ) :
    ∃ M : ℝ, 0≤M ∧ ∀ y∈Ioo (x-1) (x+1), ∀ r∈uIcc 0 t,
      ‖parameterTrajectorySlope hz x y r‖≤M := by
  have hdf : Continuous (deriv (parameterField z)) :=
    (contDiff_infty_iff_deriv.mp (parameterField_smooth hz)).2.continuous
  obtain ⟨B,hB⟩ := (isCompact_Icc (a := x-1-|t|) (b := x+1+|t|)).exists_bound_of_continuousOn
    hdf.continuousOn
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro y hy r hr
  have hxw := parameterFlow_mem_compact_window hz
    (show x∈Ioo (x-1) (x+1) by constructor <;> linarith) hr
  have hyw := parameterFlow_mem_compact_window hz hy hr
  have hbound : ∀ u∈Icc (x-1-|t|) (x+1+|t|), ‖deriv (parameterField z) u‖≤max 0 B :=
    fun u hu => (hB u hu).trans (le_max_right _ _)
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u (_ : u∈Icc (x-1-|t|) (x+1+|t|)) =>
      ((parameterField_smooth hz).differentiable (by simp) u).hasDerivAt.hasDerivWithinAt)
    hbound (convex_Icc _ _) hxw hyw
  rw [parameterTrajectorySlope,slope_def_field,norm_div]
  by_cases he : parameterFlow hz r y=parameterFlow hz r x
  · simp only [he,sub_self,norm_zero,zero_div]
    exact le_max_left _ _
  · exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr he))).mpr hh

theorem parameterTrajectorySlope_integral_tendsto (x t : ℝ) :
    Tendsto (fun y => ∫ r in 0..t, parameterTrajectorySlope hz x y r) (𝓝[≠] x)
      (𝓝 (∫ r in 0..t, deriv (parameterField z) (parameterFlow hz r x))) := by
  obtain ⟨M,_,hM⟩ := parameterTrajectorySlope_local_bound hz x t
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact (parameterTrajectorySlope_continuous hz hy).aestronglyMeasurable
  · have hn : Ioo (x-1) (x+1) ∈ 𝓝[≠] x :=
      mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith))
    filter_upwards [hn] with y hy
    filter_upwards with r hr
    exact hM y hy r (uIoc_subset_uIcc hr)
  · exact intervalIntegrable_const
  · filter_upwards with r _
    exact parameterTrajectorySlope_tendsto hz x r

def parameterJacobian (t x : ℝ) : ℝ :=
  Real.exp (∫ r in 0..t, deriv (parameterField z) (parameterFlow hz r x))

theorem parameterFlow_hasDerivAt_initial (t x : ℝ) :
    HasDerivAt (parameterFlow hz t) (parameterJacobian hz t x) x := by
  rw [hasDerivAt_iff_tendsto_slope]
  have h := (Real.continuous_exp.tendsto _).comp (parameterTrajectorySlope_integral_tendsto hz x t)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (parameterFlow_slope hz hy t).symm

theorem parameterJacobian_pos (t x : ℝ) : 0<parameterJacobian hz t x := Real.exp_pos _

theorem parameterFlow_spatial_derivative_pos (t x : ℝ) : 0<deriv (parameterFlow hz t) x := by
  rw [(parameterFlow_hasDerivAt_initial hz t x).deriv]
  exact parameterJacobian_pos hz t x

end
end OpenTranslator.TranslatorParameter

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`OpenTranslator).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Parameter spatial audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Parameter spatial audit passed for {count} declarations."
