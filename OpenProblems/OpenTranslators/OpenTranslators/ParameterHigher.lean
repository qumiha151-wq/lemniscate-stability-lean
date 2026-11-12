import OpenTranslators.ParameterSpatial
import OpenTranslators.ParameterPartialDerivatives
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Joint smoothness is bootstrapped from the proved initial-value derivative,
whose positive exponential formula is valid even where the scalar field vanishes. -/
namespace OpenTranslator.TranslatorParameter
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

section CompactIntegral
variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [NormedSpace ℝ E] [CompleteSpace V] in
theorem continuous_intervalIntegral_parameter {F : E × ℝ → V}
    (hF : Continuous F) (a b : ℝ) : Continuous (fun x => ∫ r in a..b, F (x,r)) := by
  have h (u v : ℝ) : Continuous (fun x => ∫ r in Icc u v, F (x,r)) :=
    continuous_parametric_integral_of_continuous
      (f := fun x r => F (x,r)) (μ := volume) hF isCompact_Icc
  by_cases hab : a≤b
  · simpa only [intervalIntegral.integral_of_le hab,integral_Icc_eq_integral_Ioc] using h a b
  · convert (h b a).neg using 1
    funext x
    simp only [intervalIntegral.integral_of_ge (le_of_not_ge hab),integral_Icc_eq_integral_Ioc,Pi.neg_apply]

theorem contDiff_intervalIntegral_parameter (n : ℕ) {F : E × ℝ → V}
    (hF : ContDiff ℝ n F) (a b : ℝ) : ContDiff ℝ n (fun x => ∫ r in a..b, F (x,r)) := by
  induction n generalizing V with
  | zero => exact contDiff_zero.mpr (continuous_intervalIntegral_parameter hF.continuous a b)
  | succ n ih =>
    let D : E × ℝ → E →L[ℝ] V := fun p =>
      (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hD : ContDiff ℝ n D := (hF.fderiv_right (by simp)).clm_comp contDiff_const
    rw [show (↑(n+1) : WithTop ℕ∞)=↑n+1 by simp,contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun x => ∫ r in a..b, D (x,r),ih hD,fun x => ?_⟩
    obtain ⟨M,hM⟩ := ((isCompact_closedBall x 1).prod isCompact_uIcc).bddAbove_image
      hD.continuous.norm.continuousOn
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
      (F' := fun x r => D (x,r)) (bound := fun _ => M)
      (s := Metric.closedBall x 1) (Metric.closedBall_mem_nhds x (by norm_num))
    · exact Filter.Eventually.of_forall fun y =>
        (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    · exact (hD.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr y hy
      exact hM (mem_image_of_mem _ ⟨hy,uIoc_subset_uIcc hr⟩)
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun r y _ => by
        have hp : HasFDerivAt (fun z : E => (z,r)) (ContinuousLinearMap.inl ℝ E ℝ) y := by
          convert (hasFDerivAt_id (𝕜 := ℝ) y).prodMk (hasFDerivAt_const r y) using 1 <;> rfl
        exact (hF.differentiable (by simp) (y,r)).hasFDerivAt.comp y hp
end CompactIntegral

variable {z : ℝ → TranslatorState}
variable (hz : ∀ s, HasDerivAt z (translatorNumerator (z s)) s)

theorem parameterJacobian_rescaled (t x : ℝ) :
    parameterJacobian hz t x=Real.exp
      (t*∫ r in (0:ℝ)..1, deriv (parameterField z) (parameterFlow hz (t*r) x)) := by
  unfold parameterJacobian
  congr 1
  simpa only [smul_eq_mul,mul_zero,mul_one] using
    (intervalIntegral.smul_integral_comp_mul_left
      (fun r => deriv (parameterField z) (parameterFlow hz r x)) (a := 0) (b := 1) t).symm

theorem parameterJacobian_joint_contDiff_of_flow (n : ℕ)
    (hΦ : ContDiff ℝ n (fun p : ℝ × ℝ => parameterFlow hz p.1 p.2)) :
    ContDiff ℝ n (fun p : ℝ × ℝ => parameterJacobian hz p.1 p.2) := by
  have hd : ContDiff ℝ n (deriv (parameterField z)) :=
    (contDiff_infty_iff_deriv.mp (parameterField_smooth hz)).2.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hi : ContDiff ℝ n (fun p : (ℝ × ℝ) × ℝ =>
      deriv (parameterField z) (parameterFlow hz (p.1.1*p.2) p.1.2)) :=
    hd.comp (hΦ.comp ((contDiff_fst.fst.mul contDiff_snd).prodMk contDiff_fst.snd))
  simpa only [parameterJacobian_rescaled] using
    (contDiff_fst.mul (contDiff_intervalIntegral_parameter n hi 0 1)).exp

def parameterFlowDifferential (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  parameterField z (parameterFlow hz p.1 p.2) • ContinuousLinearMap.fst ℝ ℝ ℝ+
    parameterJacobian hz p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem parameterFlow_joint_contDiff_nat (n : ℕ) :
    ContDiff ℝ n (fun p : ℝ × ℝ => parameterFlow hz p.1 p.2) := by
  induction n with
  | zero => exact contDiff_zero.mpr (parameterFlow_joint_continuous hz)
  | succ n ih =>
    have hJ := parameterJacobian_joint_contDiff_of_flow hz n ih
    have hv : ContDiff ℝ n (fun p : ℝ × ℝ => parameterField z (parameterFlow hz p.1 p.2)) :=
      ((parameterField_smooth hz).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).comp ih
    have hD : ContDiff ℝ n (parameterFlowDifferential hz) :=
      (hv.smul contDiff_const).add (hJ.smul contDiff_const)
    rw [show (↑(n+1) : ℕ∞ω)=↑n+1 by simp,contDiff_succ_iff_hasFDerivAt]
    refine ⟨parameterFlowDifferential hz,hD,fun p => ?_⟩
    have hc₁ : Continuous (fun p : ℝ × ℝ => ContinuousLinearMap.toSpanSingleton ℝ
        (parameterField z (parameterFlow hz p.1 p.2))) :=
      (ContinuousLinearMap.toSpanSingletonCLE : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ)).continuous.comp hv.continuous
    have hc₂ : Continuous (fun p : ℝ × ℝ => ContinuousLinearMap.toSpanSingleton ℝ
        (parameterJacobian hz p.1 p.2)) :=
      (ContinuousLinearMap.toSpanSingletonCLE : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ)).continuous.comp hJ.continuous
    have hp := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := p)
      (f := parameterFlow hz)
      (f₁ := fun t x => ContinuousLinearMap.toSpanSingleton ℝ (parameterField z (parameterFlow hz t x)))
      (f₂ := fun t x => ContinuousLinearMap.toSpanSingleton ℝ (parameterJacobian hz t x))
      (Filter.Eventually.of_forall fun v => (parameterFlow_derivative hz v.2 v.1).hasFDerivAt)
      (Filter.Eventually.of_forall fun v => (parameterFlow_hasDerivAt_initial hz v.1 v.2).hasFDerivAt)
      (hc₁.continuousAt (x := p)) (hc₂.continuousAt (x := p))
    have hmap :
        (ContinuousLinearMap.toSpanSingleton ℝ (parameterField z (parameterFlow hz p.1 p.2))).coprod
          (ContinuousLinearMap.toSpanSingleton ℝ (parameterJacobian hz p.1 p.2))=
        parameterFlowDifferential hz p := by
      apply ContinuousLinearMap.ext
      intro v
      change v.1*parameterField z (parameterFlow hz p.1 p.2)+v.2*parameterJacobian hz p.1 p.2=
        parameterField z (parameterFlow hz p.1 p.2)*v.1+parameterJacobian hz p.1 p.2*v.2
      ring
    change HasStrictFDerivAt (fun p : ℝ × ℝ => parameterFlow hz p.1 p.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ (parameterField z (parameterFlow hz p.1 p.2))).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (parameterJacobian hz p.1 p.2))) p at hp
    rw [hmap] at hp
    exact hp.hasFDerivAt

theorem parameterFlow_joint_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => parameterFlow hz p.1 p.2) := by
  rw [contDiff_iff_forall_nat_le]
  intro n _
  exact parameterFlow_joint_contDiff_nat hz n

theorem parameterFlow_spatial_smooth (t : ℝ) : ContDiff ℝ ∞ (parameterFlow hz t) :=
  (parameterFlow_joint_smooth hz).comp (contDiff_const.prodMk contDiff_id)

/-- An actual increasing homeomorphism with smooth forward and inverse maps.
Together with the proved positive spatial derivative this is a C-infinity
diffeomorphism, including at all stationary points of the parameter field. -/
theorem parameterFlow_diffeomorphism (t : ℝ) :
    Function.Bijective (parameterFlow hz t) ∧
      ContDiff ℝ ∞ (parameterFlow hz t) ∧ ContDiff ℝ ∞ (parameterFlow hz (-t)) ∧
      (∀ x, parameterFlow hz (-t) (parameterFlow hz t x)=x) ∧
      (∀ x, parameterFlow hz t (parameterFlow hz (-t) x)=x) ∧
      (∀ x, 0<deriv (parameterFlow hz t) x) :=
  ⟨parameterFlow_bijective hz t,parameterFlow_spatial_smooth hz t,
    parameterFlow_spatial_smooth hz (-t),parameterFlow_inverse hz t,
    fun x => by simpa only [neg_neg] using parameterFlow_inverse hz (-t) x,
    parameterFlow_spatial_derivative_pos hz t⟩

end
end OpenTranslator.TranslatorParameter

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`OpenTranslator).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Parameter higher audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Parameter higher audit passed for {count} declarations."
