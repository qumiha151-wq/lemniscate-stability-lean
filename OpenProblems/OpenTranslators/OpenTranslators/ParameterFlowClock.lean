import OpenTranslators.ParameterField

/-! The actual regularized scalar parameter flow has a surjective clock.
Its inverse constructs the original scalar flow for every real time. -/
namespace OpenTranslator.TranslatorParameter
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

def parameterClock (z : ℝ → TranslatorState) (ψ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in 0..t, 1/parameterDenominator z (ψ u)

def parameterRadius (z : ℝ → TranslatorState) (ψ : ℝ → ℝ) (t : ℝ) : ℝ :=
  energyRadius (z (ψ t) 1) (z (ψ t) 2)

def parameterRadiusRate (z : ℝ → TranslatorState) (ψ : ℝ → ℝ) (t : ℝ) : ℝ :=
  (z (ψ t) 2*Real.sin (z (ψ t) 0)/(2*parameterRadius z ψ t))*
    regularizedParameterField z (ψ t)

variable {z : ℝ → TranslatorState}
variable (hz : ∀ s, HasDerivAt z (translatorNumerator (z s)) s)
variable {ψ : ℝ → ℝ}
variable (hψ : ∀ t, HasDerivAt ψ (regularizedParameterField z (ψ t)) t)
include hz hψ

theorem parameterClock_hasDerivAt (t : ℝ) :
    HasDerivAt (parameterClock z ψ) (1/parameterDenominator z (ψ t)) t := by
  have hcont : Continuous ψ := continuous_iff_continuousAt.mpr fun u => (hψ u).continuousAt
  have hc : Continuous (fun u => 1/parameterDenominator z (ψ u)) :=
    continuous_const.div ((parameterDenominator_smooth hz).continuous.comp hcont)
      (fun u => regularizingDenominator_ne_zero (z (ψ u)))
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem parameterRadius_hasDerivAt (t : ℝ) :
    HasDerivAt (parameterRadius z ψ) (parameterRadiusRate z ψ t) t := by
  have hr := energyRadius_hasDerivAt (fun s => z s 0) (fun s => z s 1)
    (fun s => z s 2) (ψ t) (TranslatorGeometry.curvature_hasDerivAt hz (ψ t))
    (TranslatorGeometry.curvatureDerivative_hasDerivAt hz (ψ t))
  exact hr.comp t (hψ t)

omit hz hψ in
theorem parameterRadiusRate_abs_le (z : ℝ → TranslatorState) (ψ : ℝ → ℝ) (t : ℝ) :
    |parameterRadiusRate z ψ t| ≤ 1/parameterDenominator z (ψ t) := by
  have hr : |z (ψ t) 2*Real.sin (z (ψ t) 0)/(2*parameterRadius z ψ t)| ≤ 1 := by
    exact energyRadius_derivative_norm_le_one (z (ψ t) 0) (z (ψ t) 1) (z (ψ t) 2)
  have hD : 0<parameterDenominator z (ψ t) := regularizingDenominator_pos (z (ψ t))
  rw [parameterRadiusRate,abs_mul]
  calc
    _ ≤ 1*|regularizedParameterField z (ψ t)| :=
      mul_le_mul_of_nonneg_right hr (abs_nonneg _)
    _ = |parameterField z (ψ t)| / parameterDenominator z (ψ t) := by
      rw [one_mul,regularizedParameterField,abs_div,abs_of_pos hD]
    _ ≤ _ := div_le_div_of_nonneg_right (parameterField_abs_le_one z (ψ t)) hD.le

theorem parameterClock_strictMono : StrictMono (parameterClock z ψ) :=
  strictMono_of_hasDerivAt_pos (parameterClock_hasDerivAt hz hψ)
    (fun t => one_div_pos.mpr (regularizingDenominator_pos (z (ψ t))))

theorem parameterClock_surjective : Function.Surjective (parameterClock z ψ) := by
  apply clock_surjective
    (R := parameterRadius z ψ) (D := fun t => parameterDenominator z (ψ t))
    (r := parameterRadiusRate z ψ)
    (by simp [parameterClock])
    (fun t => energyRadius_pos (z (ψ t) 1) (z (ψ t) 2))
    (fun t => regularizingDenominator_pos (z (ψ t)))
    (parameterClock_hasDerivAt hz hψ) (parameterRadius_hasDerivAt hz hψ)
    (parameterRadiusRate_abs_le z ψ)
  exact fun t => denominator_le_twice_radius_sq (fun u => z (ψ u)) t

def parameterClockOrderIso : ℝ ≃o ℝ :=
  (parameterClock_strictMono hz hψ).orderIsoOfSurjective (parameterClock z ψ)
    (parameterClock_surjective hz hψ)

theorem inverseParameterClock_hasDerivAt (t : ℝ) :
    HasDerivAt (parameterClockOrderIso hz hψ).symm
      (parameterDenominator z (ψ ((parameterClockOrderIso hz hψ).symm t))) t := by
  let e := parameterClockOrderIso hz hψ
  have hh := HasDerivAt.of_local_left_inverse e.symm.toHomeomorph.continuous.continuousAt
    (parameterClock_hasDerivAt hz hψ (e.symm t))
    (one_div_ne_zero (regularizingDenominator_ne_zero _))
    (Filter.Eventually.of_forall (fun s => e.apply_symm_apply s))
  convert hh using 1 <;> first | rfl | (simp only [one_div,inv_inv]; rfl)

theorem reparametrizedParameterFlow_hasDerivAt (t : ℝ) :
    HasDerivAt (fun u => ψ ((parameterClockOrderIso hz hψ).symm u))
      (parameterField z (ψ ((parameterClockOrderIso hz hψ).symm t))) t := by
  have hh := (hψ ((parameterClockOrderIso hz hψ).symm t)).comp t
    (inverseParameterClock_hasDerivAt hz hψ t)
  convert hh using 1 <;> first | rfl | (dsimp [regularizedParameterField]; field_simp [parameterDenominator,regularizingDenominator_ne_zero])

omit hψ in
theorem exists_global_parameter_flow (u₀ : ℝ) :
    ∃ φ : ℝ → ℝ, φ 0=u₀ ∧ ∀ t, HasDerivAt φ (parameterField z (φ t)) t := by
  obtain ⟨ψ,hψ,_⟩ := exists_unique_global_bounded_flow
    (regularizedParameterField_lipschitz hz) (M := 1)
    (regularizedParameterField_norm_le z) u₀
  let e := parameterClockOrderIso hz hψ.2
  have he0 : e 0=0 := by simp [e,parameterClockOrderIso,parameterClock]
  have hinv0 : e.symm 0=0 := by simpa only [he0] using e.symm_apply_apply 0
  refine ⟨fun t => ψ (e.symm t),?_,reparametrizedParameterFlow_hasDerivAt hz hψ.2⟩
  simpa only [hinv0] using hψ.1

omit hψ in
theorem exists_unique_global_parameter_flow (u₀ : ℝ) :
    ∃! φ : ℝ → ℝ, φ 0=u₀ ∧ ∀ t, HasDerivAt φ (parameterField z (φ t)) t := by
  obtain ⟨φ,hφ0,hφ⟩ := exists_global_parameter_flow hz u₀
  refine ⟨φ,⟨hφ0,hφ⟩,?_⟩
  intro χ hχ
  have hC1 : ContDiff ℝ 1 (parameterField z) := (parameterField_smooth hz).of_le (by simp)
  exact unique_global_of_locallyLipschitz hC1.locallyLipschitz hχ.2 hφ (hχ.1.trans hφ0.symm)

end
end OpenTranslator.TranslatorParameter

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`OpenTranslator).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Parameter clock audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Parameter clock audit passed for {count} declarations."
