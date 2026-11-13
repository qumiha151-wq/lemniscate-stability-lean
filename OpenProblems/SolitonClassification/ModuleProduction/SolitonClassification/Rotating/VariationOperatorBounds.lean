module

public import SolitonClassification.Rotating.VariationLinearity
public import SolitonClassification.Rotating.UniversalVariationMajorantBudget

@[expose] public section

/-! Operator bounds from genuinely uniform arbitrary-vector estimates.
No factor six is needed in this analytic conversion. This says nothing
about numeric entrywise rounding, whose operator conversion is separate. -/
namespace SolitonClassification.Rotating
noncomputable section
open UniversalMajorant
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

def mixedVariationResidualMap (a : State) (M N : ℕ) (t : ℝ) : State →L[ℝ] State :=
  variationVelocityMap a N t-
    (fderiv ℝ field (polynomialPath (taylorPolynomial a M) t)).comp (variationPolynomialMap a N t)

theorem mixedVariationResidualMap_apply (a v : State) (M N : ℕ) (t : ℝ) :
    mixedVariationResidualMap a M N t v=polynomialPath (mixedVariationResidual a v M N) t := by
  simp only [mixedVariationResidualMap,sub_apply,ContinuousLinearMap.comp_apply,
    variationVelocityMap_apply,variationPolynomialMap_apply]
  exact (mixedVariationResidual_actual a v M N t).symm

theorem variationPolynomialMap30_norm {a : State} (ha : a∈innerTube) {t : ℝ}
    (ht : |t|≤(universalStepCap:ℝ)) : ‖variationPolynomialMap a 30 t‖≤6/5 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  rw [variationPolynomialMap_apply]
  exact (variationPolynomial30_uniform ha v ht).trans_eq (mul_comm _ _)

theorem mixedVariationResidualMap60_30_norm {a : State} (ha : a∈innerTube) {t : ℝ}
    (ht : |t|≤(universalStepCap:ℝ)) : ‖mixedVariationResidualMap a 60 30 t‖≤4/10^27 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [mixedVariationResidualMap_apply]
  exact (mixedVariationResidual60_30_uniform ha v ht).trans_eq (mul_comm _ _)

theorem mixedVariationResidualMap60_30_comp_norm {a : State} (ha : a∈innerTube) {t : ℝ}
    (ht : |t|≤(universalStepCap:ℝ)) (B : State →L[ℝ] State) :
    ‖(mixedVariationResidualMap a 60 30 t).comp B‖≤(4/10^27)*‖B‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (mixedVariationResidualMap60_30_norm ha ht) (norm_nonneg B))

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.mixedVariationResidualMap60_30_norm
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Uniform arbitrary-vector to operator bound audit passed for {count} declarations."

end
