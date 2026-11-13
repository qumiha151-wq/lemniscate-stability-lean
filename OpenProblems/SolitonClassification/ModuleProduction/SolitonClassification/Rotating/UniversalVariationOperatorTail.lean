module

public import SolitonClassification.Rotating.VariationOperatorBounds
public import SolitonClassification.Rotating.UniversalVariationTrueTail

@[expose] public section

/-! Full six-dimensional actual variational truncation in operator norm.
The arbitrary-vector tail and genuine polynomial linearity remove any
analytic column-count loss. Numeric entrywise uncertainty is separate. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set UniversalMajorant
set_option Elab.async false
set_option maxRecDepth 100000

theorem universal_signed_trueVariation60_30_operator_error (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) {t : ℝ} (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    ‖fderiv ℝ (supportFlow σ hσ t) a-variationPolynomialMap a 30 (σ*t)‖≤(7:ℝ)/10^29 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  simp only [sub_apply,variationPolynomialMap_apply]
  exact (universal_signed_trueVariation60_30_error σ hσ ha v ht).trans_eq (mul_comm _ _)

theorem universal_signed_trueVariation60_30_composed_error (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) {t : ℝ} (ht : t∈Icc 0 (universalStepCap:ℝ))
    (B : State →L[ℝ] State) :
    ‖(fderiv ℝ (supportFlow σ hσ t) a).comp B-
      (variationPolynomialMap a 30 (σ*t)).comp B‖≤((7:ℝ)/10^29)*‖B‖ := by
  have he : (fderiv ℝ (supportFlow σ hσ t) a).comp B-
      (variationPolynomialMap a 30 (σ*t)).comp B=
      (fderiv ℝ (supportFlow σ hσ t) a-variationPolynomialMap a 30 (σ*t)).comp B := by
    exact (ContinuousLinearMap.sub_comp _ _ _).symm
  rw [he]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (universal_signed_trueVariation60_30_operator_error σ hσ ha ht)
      (norm_nonneg B))

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.universal_signed_trueVariation60_30_operator_error
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Universal actual full-matrix tail audit passed for {count} declarations."

end
