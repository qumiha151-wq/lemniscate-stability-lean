import CentroidEscape.ParameterFlow
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace CentroidEscape
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false

def trajectorySlope (G : ParameterFieldData) (x y t : ℝ) : ℝ :=
  slope G.field (parameterFlow G t x) (parameterFlow G t y)

lemma trajectorySlope_continuous (G : ParameterFieldData) {x y : ℝ} (hxy : y ≠ x) :
    Continuous (trajectorySlope G x y) := by
  unfold trajectorySlope
  simp only [slope_def_field]
  apply ((G.lip.continuous.comp (parameterFlow_time_continuous G y)).sub
    (G.lip.continuous.comp (parameterFlow_time_continuous G x))).div
    ((parameterFlow_time_continuous G y).sub (parameterFlow_time_continuous G x))
  intro t
  exact sub_ne_zero.mpr (fun h => hxy ((parameterFlow_bijective G t).1 h))

lemma trajectorySlope_bound (G : ParameterFieldData) (x y t : ℝ) :
    ‖trajectorySlope G x y t‖ ≤ G.K := by
  unfold trajectorySlope
  rw [slope_def_field, norm_div]
  by_cases h : parameterFlow G t y = parameterFlow G t x
  · simp [h]
  · apply (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr h))).2
    simpa only [dist_eq_norm, mul_comm] using
      G.lip.dist_le_mul (parameterFlow G t y) (parameterFlow G t x)

/-- The difference of two actual trajectories is solved exactly, including
across any zeros of the vector field: no division by the field is used. -/
theorem parameterFlow_difference (G : ParameterFieldData) {x y : ℝ}
    (hxy : y ≠ x) (t : ℝ) :
    parameterFlow G t y - parameterFlow G t x =
      (y-x) * Real.exp (∫ r in 0..t, trajectorySlope G x y r) := by
  let A := trajectorySlope G x y
  have hAc : Continuous A := trajectorySlope_continuous G hxy
  have hv : ∀ r, LipschitzWith G.K (fun z : ℝ => A r * z) := by
    intro r
    rw [lipschitzWith_iff_dist_le_mul]
    intro z w
    rw [dist_eq_norm, ← mul_sub, norm_mul, dist_eq_norm]
    exact mul_le_mul_of_nonneg_right (trajectorySlope_bound G x y r) (norm_nonneg _)
  have hf : ∀ r, HasDerivAt (fun s => parameterFlow G s y - parameterFlow G s x)
      (A r * (parameterFlow G r y - parameterFlow G r x)) r := by
    intro r
    have he : A r * (parameterFlow G r y - parameterFlow G r x) =
        G.field (parameterFlow G r y) - G.field (parameterFlow G r x) := by
      simpa only [A, trajectorySlope, smul_eq_mul, mul_comm, vsub_eq_sub] using
        sub_smul_slope G.field (parameterFlow G r x) (parameterFlow G r y)
    rw [he]
    exact (parameterFlow_derivative G y r).sub (parameterFlow_derivative G x r)
  have hh : ∀ r, HasDerivAt
      (fun s => (y-x)*Real.exp (∫ u in 0..s, A u))
      (A r * ((y-x)*Real.exp (∫ u in 0..r, A u))) r := by
    intro r
    convert! ((hAc.integral_hasStrictDerivAt 0 r).hasDerivAt.exp).const_mul (y-x) using 1
    ring
  have he := ODE_solution_unique_univ (v := fun r z => A r * z) (s := fun _ => univ)
    (fun r => (hv r).lipschitzOnWith)
    (fun r => ⟨hf r, mem_univ _⟩) (fun r => ⟨hh r, mem_univ _⟩)
    (t₀ := 0) (by simp [parameterFlow_zero])
  exact congrFun he t

theorem parameterFlow_slope (G : ParameterFieldData) {x y : ℝ}
    (hxy : y ≠ x) (t : ℝ) :
    slope (parameterFlow G t) x y = Real.exp (∫ r in 0..t, trajectorySlope G x y r) := by
  rw [slope_def_field, parameterFlow_difference G hxy t,
    mul_div_cancel_left₀ _ (sub_ne_zero.mpr hxy)]

lemma trajectorySlope_tendsto (G : ParameterFieldData)
    (hg : Differentiable ℝ G.field) (x r : ℝ) :
    Tendsto (fun y => trajectorySlope G x y r) (𝓝[≠] x)
      (𝓝 (deriv G.field (parameterFlow G r x))) := by
  have hc : ContinuousAt (parameterFlow G r) x :=
    (parameterFlow_lipschitz G r).continuous.continuousAt
  have hn : Tendsto (parameterFlow G r) (𝓝[≠] x) (𝓝[≠] parameterFlow G r x) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨hc.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact fun h => hy ((parameterFlow_bijective G r).1 h)
  exact (hasDerivAt_iff_tendsto_slope.mp (hg _).hasDerivAt).comp hn

theorem trajectorySlope_integral_tendsto (G : ParameterFieldData)
    (hg : Differentiable ℝ G.field) (x t : ℝ) :
    Tendsto (fun y => ∫ r in 0..t, trajectorySlope G x y r) (𝓝[≠] x)
      (𝓝 (∫ r in 0..t, deriv G.field (parameterFlow G r x))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => (G.K : ℝ))
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact (trajectorySlope_continuous G hy).aestronglyMeasurable
  · filter_upwards with y
    filter_upwards with r _
    exact trajectorySlope_bound G x y r
  · exact intervalIntegrable_const
  · filter_upwards with r _
    exact trajectorySlope_tendsto G hg x r

def parameterJacobian (G : ParameterFieldData) (t x : ℝ) : ℝ :=
  Real.exp (∫ r in 0..t, deriv G.field (parameterFlow G r x))

/-- True differentiability with respect to the initial parameter. The
derivative is positive even at stationary points of the scalar field. -/
theorem parameterFlow_hasDerivAt_initial (G : ParameterFieldData)
    (hg : Differentiable ℝ G.field) (t x : ℝ) :
    HasDerivAt (parameterFlow G t) (parameterJacobian G t x) x := by
  rw [hasDerivAt_iff_tendsto_slope]
  have h := (Real.continuous_exp.tendsto _).comp (trajectorySlope_integral_tendsto G hg x t)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (parameterFlow_slope G hy t).symm

theorem parameterJacobian_pos (G : ParameterFieldData) (t x : ℝ) :
    0 < parameterJacobian G t x := Real.exp_pos _

theorem parameterJacobian_continuous (G : ParameterFieldData)
    (hg' : Continuous (deriv G.field)) (t : ℝ) :
    Continuous (parameterJacobian G t) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hi : Tendsto (fun y => ∫ r in 0..t, deriv G.field (parameterFlow G r y)) (𝓝 x)
      (𝓝 (∫ r in 0..t, deriv G.field (parameterFlow G r x))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (G.K : ℝ))
    · filter_upwards with y
      exact (hg'.comp (parameterFlow_time_continuous G y)).aestronglyMeasurable
    · filter_upwards with y
      filter_upwards with r _
      exact norm_deriv_le_of_lipschitz G.lip
    · exact intervalIntegrable_const
    · filter_upwards with r _
      exact hg'.continuousAt.tendsto.comp (parameterFlow_lipschitz G r).continuous.continuousAt.tendsto
  exact Real.continuous_exp.continuousAt.tendsto.comp hi

theorem parameterFlow_C1 (G : ParameterFieldData)
    (hg : ContDiff ℝ 1 G.field) (t : ℝ) : ContDiff ℝ 1 (parameterFlow G t) := by
  rw [contDiff_one_iff_deriv] at hg ⊢
  refine ⟨fun x => (parameterFlow_hasDerivAt_initial G hg.1 t x).differentiableAt, ?_⟩
  have hd : deriv (parameterFlow G t) = parameterJacobian G t := by
    funext x
    exact (parameterFlow_hasDerivAt_initial G hg.1 t x).deriv
  rw [hd]
  exact parameterJacobian_continuous G hg.2 t

/-- Both the actual homeomorphism and its inverse are C1. -/
theorem parameterFlowHomeomorph_C1 (G : ParameterFieldData)
    (hg : ContDiff ℝ 1 G.field) (t : ℝ) :
    ContDiff ℝ 1 (parameterFlowHomeomorph G t) ∧
      ContDiff ℝ 1 (parameterFlowHomeomorph G t).symm :=
  ⟨parameterFlow_C1 G hg t, parameterFlow_C1 G hg (-t)⟩

theorem profileParameterField_C1 {q : ℝ → State}
    (hq : ∀ s, HasDerivAt q (field (q s)) s) : ContDiff ℝ 1 (parameterField q) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun s => (parameterField_hasDerivAt hq s).differentiableAt, ?_⟩
  have hd : deriv (parameterField q) = parameterFieldDerivative q := by
    funext s
    exact (parameterField_hasDerivAt hq s).deriv
  rw [hd]
  have hc : Continuous q := continuous_iff_continuousAt.mpr fun s => (hq s).continuousAt
  unfold parameterFieldDerivative
  fun_prop

theorem profileParameterLift_C1 {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hp : Function.Periodic q P) (hP : P ≠ 0) (t : ℝ) :
    ContDiff ℝ 1 (profileParameterLift hq hp hP t) :=
  parameterFlow_C1 (profileParameterData hq hp hP) (profileParameterField_C1 hq) _

theorem profileParameterLift_initial_derivative {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hp : Function.Periodic q P) (hP : P ≠ 0) (t s : ℝ) :
    HasDerivAt (profileParameterLift hq hp hP t)
      (parameterJacobian (profileParameterData hq hp hP) (logarithmicTime t) s) s :=
  parameterFlow_hasDerivAt_initial (profileParameterData hq hp hP)
    (fun s => (parameterField_hasDerivAt hq s).differentiableAt) _ _

/-- The reparametrized curve has a genuine, everywhere positive spatial speed,
strengthening the earlier a.e. identity. -/
theorem reparametrized_spatial_speed_pos {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hu : ∀ s, tangentSquare (q s) = 1)
    (hp : Function.Periodic q P) (hP : P ≠ 0) {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    0 < ‖deriv (fun r => expandingCurve q t (profileParameterLift hq hp hP t r)) s‖ := by
  have hφ := profileParameterLift_initial_derivative hq hp hP t s
  have hd := (expandingCurve_space_derivative hq t
    (profileParameterLift hq hp hP t s)).scomp s hφ
  have hd' : HasDerivAt (fun r => expandingCurve q t (profileParameterLift hq hp hP t r))
      (parameterJacobian (profileParameterData hq hp hP) (logarithmicTime t) s •
        (expanderRadius t • tangent (q (profileParameterLift hq hp hP t s)))) s := by
    convert! hd using 1
  rw [hd'.deriv, norm_smul, norm_smul, tangent_norm_one (hu _),
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (parameterJacobian_pos _ _ _), abs_of_pos (expanderRadius_pos ht), mul_one]
  exact mul_pos (parameterJacobian_pos _ _ _) (expanderRadius_pos ht)

end
end CentroidEscape

#print axioms CentroidEscape.parameterFlow_hasDerivAt_initial
#print axioms CentroidEscape.parameterFlowHomeomorph_C1
#print axioms CentroidEscape.reparametrized_spatial_speed_pos

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Centroid spatial-regularity audit passed for {checked} declarations."
