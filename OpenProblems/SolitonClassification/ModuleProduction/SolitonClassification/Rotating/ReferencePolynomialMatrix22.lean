module

public import SolitonClassification.Rotating.ReferencePolynomialMatrix
public import SolitonClassification.Rotating.UniversalVariationOrder22

@[expose] public section

/-! Order-22 specialization of the genuine operator and inverse bridges.
It reuses state order 60 and preserves every coordinate of the full matrix. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set UniversalMajorant
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

theorem variationPolynomialMap22_norm {a : State} (ha : a∈innerTube) {t : ℝ}
    (ht : |t|≤(universalStepCap:ℝ)) : ‖variationPolynomialMap a 22 t‖≤6/5 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  rw [variationPolynomialMap_apply]
  exact (variationPolynomial22_uniform ha v ht).trans_eq (mul_comm _ _)

theorem mixedVariationResidualMap60_22_norm {a : State} (ha : a∈innerTube) {t : ℝ}
    (ht : |t|≤(universalStepCap:ℝ)) : ‖mixedVariationResidualMap a 60 22 t‖≤2/10^19 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [mixedVariationResidualMap_apply]
  exact (mixedVariationResidual60_22_uniform ha v ht).trans_eq (mul_comm _ _)

theorem universal_signed_trueVariation60_22_operator_error (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) {t : ℝ} (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    ‖fderiv ℝ (supportFlow σ hσ t) a-variationPolynomialMap a 22 (σ*t)‖≤(4:ℝ)/10^21 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  simp only [sub_apply,variationPolynomialMap_apply]
  exact (universal_signed_trueVariation60_22_error σ hσ ha v ht).trans_eq (mul_comm _ _)

theorem variationVelocityMap22_norm {a : State} (ha : a∈innerTube) {t : ℝ}
    (ht : |t|≤(universalStepCap:ℝ)) : ‖variationVelocityMap a 22 t‖≤107/5 :=
  variationVelocityMap_norm_of_bounds (taylorPolynomial60_tube_uniform ha ht)
    (variationPolynomialMap22_norm ha ht) ((mixedVariationResidualMap60_22_norm ha ht).trans (by norm_num))

theorem variationPolynomialMap22_unit (σ : ℝ) (hσ : |σ|≤1) {a : State} (ha : a∈innerTube)
    {t : ℝ} (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    IsUnit (variationPolynomialMap a 22 (σ*t)) ∧
      ‖Ring.inverse (variationPolynomialMap a 22 (σ*t))‖≤5/4 := by
  apply variationPolynomialMap_unit_of_velocity_bound σ hσ a 22 le_rfl ht
  intro s hs
  apply variationVelocityMap22_norm ha
  rw [abs_mul,abs_of_nonneg hs.1]
  exact (mul_le_mul_of_nonneg_right hσ hs.1).trans (by simpa using hs.2)

theorem referencePolynomialMatrix22_bounds (σ : ℝ) (hσ : |σ|≤1) {a : State} (ha : a∈innerTube)
    (B : State →L[ℝ] State) (hB : IsUnit B) {t : ℝ} (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    IsUnit (referencePolynomialMatrix σ a 22 B t) ∧
      ‖referencePolynomialMatrix σ a 22 B t‖≤(6/5)*‖B‖ ∧
      ‖Ring.inverse (referencePolynomialMatrix σ a 22 B t)‖≤(5/4)*‖Ring.inverse B‖ := by
  have hu:=variationPolynomialMap22_unit σ hσ ha ht
  have hs : |σ*t|≤(universalStepCap:ℝ) := by
    rw [abs_mul,abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right hσ ht.1).trans (by simpa using ht.2)
  change IsUnit (variationPolynomialMap a 22 (σ*t)*B) ∧ _
  refine ⟨hu.1.mul hB,?_,?_⟩
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (variationPolynomialMap22_norm ha hs) (norm_nonneg B))
  · change ‖Ring.inverse (variationPolynomialMap a 22 (σ*t)*B)‖≤_
    rw [Ring.inverse_mul (Or.inl hu.1)]
    exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left hu.2 (norm_nonneg _)).trans_eq (mul_comm _ _))

theorem referencePolynomialMatrix22_residual_norm (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) (B : State →L[ℝ] State) {t : ℝ}
    (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    ‖σ • ((mixedVariationResidualMap a 60 22 (σ*t)).comp B)‖≤(2/10^19)*‖B‖ := by
  have hs : |σ*t|≤(universalStepCap:ℝ) := by
    rw [abs_mul,abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right hσ ht.1).trans (by simpa using ht.2)
  rw [norm_smul,Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_right hσ (norm_nonneg _)).trans
  simp only [one_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (mixedVariationResidualMap60_22_norm ha hs) (norm_nonneg B))

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.referencePolynomialMatrix22_bounds
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Order-22 full-operator and reference-inverse audit passed for {count} declarations."

end
