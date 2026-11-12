import CentroidEscape.SmoothReparam
import Mathlib.Analysis.Calculus.ParametricIntegral
import CentroidEscape.PartialDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace CentroidEscape
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal Interval ContDiff
set_option backward.isDefEq.respectTransparency false

section CompactIntegral
variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [NormedSpace ℝ E] [CompleteSpace V] in
lemma continuous_intervalIntegral_parameter {F : E × ℝ → V}
    (hF : Continuous F) (a b : ℝ) :
    Continuous (fun x => ∫ r in a..b, F (x,r)) := by
  have h (u v : ℝ) : Continuous (fun x => ∫ r in Icc u v, F (x,r)) :=
    continuous_parametric_integral_of_continuous
      (f := fun x r => F (x,r)) (μ := volume) hF isCompact_Icc
  by_cases hab : a ≤ b
  · simpa only [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
      using h a b
  · convert (h b a).neg using 1
    funext x
    simp only [intervalIntegral.integral_of_ge (le_of_not_ge hab),
      integral_Icc_eq_integral_Ioc, Pi.neg_apply]

/-- Integration over a fixed compact interval preserves every finite order of
regularity. The local derivative bound is obtained from compactness, rather
than imposed on the integrand. -/
theorem contDiff_intervalIntegral_parameter (n : ℕ) {F : E × ℝ → V}
    (hF : ContDiff ℝ n F) (a b : ℝ) :
    ContDiff ℝ n (fun x => ∫ r in a..b, F (x,r)) := by
  induction n generalizing V with
  | zero => exact contDiff_zero.mpr (continuous_intervalIntegral_parameter hF.continuous a b)
  | succ n ih =>
    let D : E × ℝ → E →L[ℝ] V := fun p =>
      (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hD : ContDiff ℝ n D :=
      (hF.fderiv_right (by simp)).clm_comp contDiff_const
    rw [show (↑(n+1) : WithTop ℕ∞) = (↑n + 1) by simp,
      contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun x => ∫ r in a..b, D (x,r), ih hD, fun x => ?_⟩
    obtain ⟨M, hM⟩ := ((isCompact_closedBall x 1).prod (isCompact_uIcc)).bddAbove_image
      hD.continuous.norm.continuousOn
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
      (F' := fun x r => D (x,r)) (bound := fun _ => M)
      (s := Metric.closedBall x 1) (Metric.closedBall_mem_nhds x (by norm_num))
    · exact Filter.Eventually.of_forall fun y =>
        (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    · exact (hD.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr y hy
      exact hM (mem_image_of_mem _ ⟨hy, uIoc_subset_uIcc hr⟩)
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun r y _ => by
        have hp : HasFDerivAt (fun z : E => (z,r)) (ContinuousLinearMap.inl ℝ E ℝ) y := by
          convert (hasFDerivAt_id (𝕜 := ℝ) y).prodMk (hasFDerivAt_const r y) using 1 <;> rfl
        exact (hF.differentiable (by simp) (y,r)).hasFDerivAt.comp y hp

end CompactIntegral

lemma parameterFlow_time_lipschitz (G : ParameterFieldData) (x : ℝ) :
    LipschitzWith G.M (fun t => parameterFlow G t x) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (parameterFlow_derivative G x t).differentiableAt)
  intro t
  rw [← NNReal.coe_le_coe, coe_nnnorm, (parameterFlow_derivative G x t).deriv]
  exact G.bound _

theorem parameterFlow_joint_continuous (G : ParameterFieldData) :
    Continuous (fun p : ℝ × ℝ => parameterFlow G p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hl : Tendsto (fun z : ℝ × ℝ => (G.M : ℝ) * dist z.1 p.1 +
      Real.exp ((G.K : ℝ) * |p.1|) * dist z.2 p.2) (𝓝 p) (𝓝 0) := by
    have hc : Continuous (fun z : ℝ × ℝ => (G.M : ℝ) * dist z.1 p.1 +
        Real.exp ((G.K : ℝ) * |p.1|) * dist z.2 p.2) := by fun_prop
    simpa [ContinuousAt] using hc.continuousAt (x := p)
  have hb : ∀ z : ℝ × ℝ, dist (parameterFlow G z.1 z.2) (parameterFlow G p.1 p.2) ≤
      (G.M : ℝ) * dist z.1 p.1 + Real.exp ((G.K : ℝ) * |p.1|) * dist z.2 p.2 :=
    fun z => (dist_triangle (parameterFlow G z.1 z.2)
      (parameterFlow G p.1 z.2) (parameterFlow G p.1 p.2)).trans
      (add_le_add ((parameterFlow_time_lipschitz G z.2).dist_le_mul z.1 p.1)
        ((parameterFlow_lipschitz G p.1).dist_le_mul z.2 p.2))
  exact squeeze_zero (fun _ => dist_nonneg) hb hl

lemma parameterJacobian_rescaled (G : ParameterFieldData) (t x : ℝ) :
    parameterJacobian G t x = Real.exp
      (t * ∫ r in (0 : ℝ)..1, deriv G.field (parameterFlow G (t*r) x)) := by
  unfold parameterJacobian
  congr 1
  simpa only [smul_eq_mul, mul_zero, mul_one] using
    (intervalIntegral.smul_integral_comp_mul_left
      (fun r => deriv G.field (parameterFlow G r x)) (a := 0) (b := 1) t).symm

lemma parameterJacobian_joint_contDiff_of_flow (G : ParameterFieldData) (n : ℕ)
    (hg : ContDiff ℝ ∞ G.field)
    (hΦ : ContDiff ℝ n (fun p : ℝ × ℝ => parameterFlow G p.1 p.2)) :
    ContDiff ℝ n (fun p : ℝ × ℝ => parameterJacobian G p.1 p.2) := by
  have hdg : ContDiff ℝ n (deriv G.field) := (contDiff_infty_iff_deriv.mp hg).2.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hi : ContDiff ℝ n (fun p : (ℝ × ℝ) × ℝ =>
      deriv G.field (parameterFlow G (p.1.1*p.2) p.1.2)) :=
    hdg.comp (hΦ.comp ((contDiff_fst.fst.mul contDiff_snd).prodMk contDiff_fst.snd))
  simpa only [parameterJacobian_rescaled] using
    (contDiff_fst.mul (contDiff_intervalIntegral_parameter n hi 0 1)).exp

/-- The true derivative with respect to the pair (time, initial parameter). -/
def parameterFlowDifferential (G : ParameterFieldData) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  G.field (parameterFlow G p.1 p.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    parameterJacobian G p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem parameterFlow_joint_contDiff_nat (G : ParameterFieldData)
    (hg : ContDiff ℝ ∞ G.field) (n : ℕ) :
    ContDiff ℝ n (fun p : ℝ × ℝ => parameterFlow G p.1 p.2) := by
  induction n with
  | zero => exact contDiff_zero.mpr (parameterFlow_joint_continuous G)
  | succ n ih =>
    have hJ := parameterJacobian_joint_contDiff_of_flow G n hg ih
    have hv : ContDiff ℝ n (fun p : ℝ × ℝ => G.field (parameterFlow G p.1 p.2)) :=
      (hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).comp ih
    have hD : ContDiff ℝ n (parameterFlowDifferential G) :=
      (hv.smul contDiff_const).add (hJ.smul contDiff_const)
    rw [show (↑(n+1) : ℕ∞ω) = ↑n + 1 by simp, contDiff_succ_iff_hasFDerivAt]
    refine ⟨parameterFlowDifferential G, hD, fun p => ?_⟩
    have hc₁ : Continuous (fun p : ℝ × ℝ => ContinuousLinearMap.toSpanSingleton ℝ
        (G.field (parameterFlow G p.1 p.2))) :=
      (ContinuousLinearMap.toSpanSingletonCLE : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ)).continuous.comp hv.continuous
    have hc₂ : Continuous (fun p : ℝ × ℝ => ContinuousLinearMap.toSpanSingleton ℝ
        (parameterJacobian G p.1 p.2)) :=
      (ContinuousLinearMap.toSpanSingletonCLE : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ)).continuous.comp hJ.continuous
    have hp := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := p)
      (f := parameterFlow G)
      (f₁ := fun t x => ContinuousLinearMap.toSpanSingleton ℝ (G.field (parameterFlow G t x)))
      (f₂ := fun t x => ContinuousLinearMap.toSpanSingleton ℝ (parameterJacobian G t x))
      (Filter.Eventually.of_forall fun v => (parameterFlow_derivative G v.2 v.1).hasFDerivAt)
      (Filter.Eventually.of_forall fun v =>
        (parameterFlow_hasDerivAt_initial G (hg.differentiable (by simp)) v.1 v.2).hasFDerivAt)
      (hc₁.continuousAt (x := p)) (hc₂.continuousAt (x := p))
    have hmap :
        (ContinuousLinearMap.toSpanSingleton ℝ (G.field (parameterFlow G p.1 p.2))).coprod
          (ContinuousLinearMap.toSpanSingleton ℝ (parameterJacobian G p.1 p.2)) =
        parameterFlowDifferential G p := by
      apply ContinuousLinearMap.ext
      intro v
      change v.1 * G.field (parameterFlow G p.1 p.2) + v.2 * parameterJacobian G p.1 p.2 =
        G.field (parameterFlow G p.1 p.2) * v.1 + parameterJacobian G p.1 p.2 * v.2
      ring
    change HasStrictFDerivAt (fun p : ℝ × ℝ => parameterFlow G p.1 p.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ (G.field (parameterFlow G p.1 p.2))).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (parameterJacobian G p.1 p.2))) p at hp
    rw [hmap] at hp
    exact hp.hasFDerivAt

/-- The actual complete scalar flow is jointly smooth, including points where
the vector field vanishes. This is deduced from the existing unique flow and
the exponential formula for its initial-value derivative. -/
theorem parameterFlow_joint_smooth (G : ParameterFieldData)
    (hg : ContDiff ℝ ∞ G.field) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => parameterFlow G p.1 p.2) := by
  rw [contDiff_iff_forall_nat_le]
  intro n _
  exact parameterFlow_joint_contDiff_nat G hg n

theorem parameterFlowHomeomorph_smooth (G : ParameterFieldData)
    (hg : ContDiff ℝ ∞ G.field) (t : ℝ) :
    ContDiff ℝ ∞ (parameterFlowHomeomorph G t) ∧
      ContDiff ℝ ∞ (parameterFlowHomeomorph G t).symm := by
  constructor
  · exact (parameterFlow_joint_smooth G hg).comp (contDiff_const.prodMk contDiff_id)
  · exact (parameterFlow_joint_smooth G hg).comp (contDiff_const.prodMk contDiff_id)

/-- Polynomial ODE regularity supplies smoothness of the profile; it is not a
new regularity premise on the exact orbit. -/
theorem globalProfile_smooth {q : ℝ → State}
    (hq : ∀ s, HasDerivAt q (field (q s)) s) : ContDiff ℝ ∞ q := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hd : ContDiffOn ℝ ∞ q (Icc (t-1) (t+1)) := by
    apply ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
      (f := fun (_ : ℝ) z => field z) (u := univ)
    · exact ((field_smooth ⊤).comp contDiff_snd).contDiffOn
    · intro s _
      exact (hq s).hasDerivWithinAt
    · intro s _
      exact mem_univ _
  exact hd.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))

theorem profileParameterField_smooth {q : ℝ → State}
    (hq : ∀ s, HasDerivAt q (field (q s)) s) : ContDiff ℝ ∞ (parameterField q) := by
  have h := globalProfile_smooth hq
  exact (((contDiff_apply ℝ ℝ 0).comp h).mul ((contDiff_apply ℝ ℝ 2).comp h) |>.add
    (((contDiff_apply ℝ ℝ 1).comp h).mul ((contDiff_apply ℝ ℝ 3).comp h))).neg

theorem profileParameterLift_smooth {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hp : Function.Periodic q P) (hP : P ≠ 0) (t : ℝ) :
    ContDiff ℝ ∞ (profileParameterLift hq hp hP t) :=
  (parameterFlow_joint_smooth (profileParameterData hq hp hP)
    (profileParameterField_smooth hq)).comp (contDiff_const.prodMk contDiff_id)

theorem profileParameterLift_joint_smoothAt {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hp : Function.Periodic q P) (hP : P ≠ 0) {p : ℝ × ℝ} (ht : -1/4 < p.1) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => profileParameterLift hq hp hP z.1 z.2) p := by
  have hclock : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => logarithmicTime z.1) p := by
    unfold logarithmicTime
    exact ((contDiffAt_const.add (contDiffAt_const.mul contDiffAt_fst)).log
      (by linarith : (1 : ℝ) + 4*p.1 ≠ 0)).div_const 4
  exact (parameterFlow_joint_smooth (profileParameterData hq hp hP)
    (profileParameterField_smooth hq)).contDiffAt.comp p (hclock.prodMk contDiffAt_snd)

lemma position_smooth : ContDiff ℝ ∞ position := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact contDiff_apply ℝ ℝ 0
  · exact contDiff_apply ℝ ℝ 1

theorem coherentExpandingCurve_spatial_smooth {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hp : Function.Periodic q P) (hP : P ≠ 0) (t : ℝ) :
    ContDiff ℝ ∞ (coherentExpandingCurve hq hp hP t) := by
  change ContDiff ℝ ∞ (fun s => expanderRadius t • position (q (profileParameterLift hq hp hP t s)))
  have hc : ContDiff ℝ ∞ (fun _ : ℝ => expanderRadius t) := contDiff_const
  exact hc.smul (position_smooth.comp ((globalProfile_smooth hq).comp
    (profileParameterLift_smooth hq hp hP t)))

theorem coherentExpandingCurve_joint_smoothAt {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hp : Function.Periodic q P) (hP : P ≠ 0) {p : ℝ × ℝ} (ht : -1/4 < p.1) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => coherentExpandingCurve hq hp hP z.1 z.2) p := by
  have hR : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => expanderRadius z.1) p := by
    unfold expanderRadius
    exact (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_fst)).rpow_const_of_ne
      (by linarith : (1 : ℝ) + 4*p.1 ≠ 0)
  exact hR.smul (position_smooth.contDiffAt.comp p ((globalProfile_smooth hq).contDiffAt.comp p
    (profileParameterLift_joint_smoothAt hq hp hP ht)))

theorem profileParameterHomeomorph_smooth {q : ℝ → State} {P : ℝ}
    (hq : ∀ s, HasDerivAt q (field (q s)) s)
    (hp : Function.Periodic q P) (hP : P ≠ 0) (t : ℝ) :
    ContDiff ℝ ∞ (parameterFlowHomeomorph (profileParameterData hq hp hP) (logarithmicTime t)) ∧
      ContDiff ℝ ∞ (parameterFlowHomeomorph (profileParameterData hq hp hP)
        (logarithmicTime t)).symm :=
  parameterFlowHomeomorph_smooth _ (profileParameterField_smooth hq) _

/-- Exact half-orbit shooting data give a genuinely classical smooth flow
with the actual intrinsic elastic force and divergent arclength centroid.
No regularity of the parameter map is assumed. The numerical shooting input
is deliberately still explicit. -/
theorem exact_half_orbit_yields_smooth_classical_FEF_escape
    {z : ℝ → State} {m : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L)
    (hz : ∀ s ∈ Icc (0:ℝ) L, HasDerivAt z (field (z s)) s)
    (h0 : reverseState (z 0) = z 0) (hfix : reverseState (z L) = z L)
    (hu : z 0 2 = 0) (hw : z 0 3 = 1)
    (hm : ∀ s ∈ Icc (0:ℝ) L, HasDerivAt m (z s 0) s)
    (hm0 : m 0 = 0) (hmpos : 0 < m L) :
    ∃ γ : ℝ → ℝ → Plane,
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => γ p.1 p.2) {p | -1/4 < p.1} ∧
      (∀ t, Function.Periodic (γ t) (2*L) ∧ ContDiff ℝ ∞ (γ t)) ∧
      (∀ t, 0 ≤ t → ∀ s, 0 < ‖deriv (γ t) s‖) ∧
      (∀ t, 0 ≤ t → ∀ s, HasDerivAt (fun r => γ r s)
        ((-curveElasticForce (γ t) s) • curveUnitNormal (γ t) s) t) ∧
      Tendsto (fun t => curveCentroidX (2*L) (γ t)) atTop atTop := by
  obtain ⟨q, hp, _, hq, hunit, _, _, hesc⟩ :=
    exact_half_orbit_yields_centroid_escape hL hz h0 hfix hu hw hm hm0 hmpos
  have hP : 2*L ≠ 0 := by positivity
  refine ⟨coherentExpandingCurve hq hp hP, ?_, ?_, ?_, ?_, ?_⟩
  · intro p ht
    exact (coherentExpandingCurve_joint_smoothAt hq hp hP ht).contDiffWithinAt
  · intro t
    exact ⟨coherentExpandingCurve_periodic hq hp hP t,
      coherentExpandingCurve_spatial_smooth hq hp hP t⟩
  · intro t ht s
    exact reparametrized_spatial_speed_pos hq hunit hp hP ht s
  · intro t ht s
    exact coherentExpandingCurve_geometric_FEF hq hunit hp hP ht s
  · apply hesc.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact (coherentExpandingCurve_centroid hq hunit hp hP ht).symm

end
end CentroidEscape

#print axioms CentroidEscape.contDiff_intervalIntegral_parameter
#print axioms CentroidEscape.parameterFlow_joint_smooth
#print axioms CentroidEscape.exact_half_orbit_yields_smooth_classical_FEF_escape

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
  logInfo m!"Centroid joint-smoothness audit passed for {checked} declarations."
