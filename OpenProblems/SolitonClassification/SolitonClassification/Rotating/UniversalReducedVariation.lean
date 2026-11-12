import SolitonClassification.Rotating.UniversalStateOrders
import SolitonClassification.Rotating.UniversalVariationOrder22
import SolitonClassification.Rotating.ReferencePolynomialMatrix

/-! Lower state orders retain the full actual variational comparison.
In particular a state42 residual is never replaced by the state60 residual.
All finite scalar bounds are exact kernel decisions; no grid is asserted. -/
namespace SolitonClassification.Rotating.UniversalMajorant
noncomputable section
open Set Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

def mixedJacResidualAtCap (M N : ℕ) : ℚ :=
  3*(122/19)*(stateScalarValueAtCap M)^2*jacValueAtCap N-jacDerivativeAtCap N

theorem reducedJacobian_budgets :
    mixedJacResidualAtCap 42 22≤2/10^19 ∧
      mixedJacResidualAtCap 44 22≤2/10^19 := by
  decide +kernel

lemma jacResidual_mixed_order_value (M N : ℕ) :
    (jacResidual M N).eval (universalStepCap:ℝ)=(mixedJacResidualAtCap M N:ℝ) := by
  simp only [jacResidual,jacLipschitzPolynomial,eval_sub,eval_mul,eval_C,eval_pow,
    scalarPolynomial_order_value,jacPolynomial_order_value,jacPolynomial_order_derivative_value]
  simp only [mixedJacResidualAtCap,rate,Rat.cast_sub,Rat.cast_mul,Rat.cast_pow,
    Rat.cast_div,Rat.cast_ofNat]

theorem mixedJacResidual_uniform {M N : ℕ} (hNM : N≤M) {ε : ℚ}
    (hb : mixedJacResidualAtCap M N≤ε) {t : ℝ} (ht : 0≤t)
    (hT : t≤(universalStepCap:ℝ)) : (jacResidual M N).eval t≤(ε:ℝ) := by
  have h:=eval_monotone_of_coeff_nonneg (fun n=>jacResidual_nonneg M N n hNM) ht hT
  rw [jacResidual_mixed_order_value] at h
  exact h.trans ((Rat.cast_le (K:=ℝ)).mpr hb)

theorem mixedVariationResidual_order_uniform {a : State} (ha : a∈innerTube)
    {M N : ℕ} (hNM : N≤M) (v : State) {ε : ℚ}
    (hb : mixedJacResidualAtCap M N≤ε) {t : ℝ} (ht : |t|≤(universalStepCap:ℝ)) :
    ‖polynomialPath (mixedVariationResidual a v M N) t‖≤‖v‖*(ε:ℝ) :=
  (mixedVariationResidual_norm_bound ha M N hNM v t).trans
    (mul_le_mul_of_nonneg_left (mixedJacResidual_uniform hNM hb (abs_nonneg t) ht) (norm_nonneg v))

theorem mixedVariationResidualMap_order_norm {a : State} (ha : a∈innerTube)
    {M N : ℕ} (hNM : N≤M) {ε : ℚ} (hε : 0≤ε)
    (hb : mixedJacResidualAtCap M N≤ε) {t : ℝ} (ht : |t|≤(universalStepCap:ℝ)) :
    ‖mixedVariationResidualMap a M N t‖≤(ε:ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by exact_mod_cast hε)
  intro v
  rw [mixedVariationResidualMap_apply]
  exact (mixedVariationResidual_order_uniform ha hNM v hb ht).trans_eq (mul_comm _ _)

theorem universal_signed_reducedVariation_error (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) {M N : ℕ} (hNM : N≤M) (hN : N≤60) (v : State)
    {εX EX εV δ : ℚ} (hεX0 : 0≤εX) (hεX1 : εX≤1) (hEX : 0≤EX) (hεV : 0≤εV)
    (hstate : stateResidualAtCap M≤εX)
    (hex : (19/2)*(stateScalarValueAtCap M-1)≤129/250)
    (hstateBudget : 2*εX*universalStepCap≤EX)
    (hV : jacValueAtCap N≤6/5) (hres : mixedJacResidualAtCap M N≤εV)
    (hbudget : 2*(4*EX*(6/5)+εV)*universalStepCap≤δ)
    {t : ℝ} (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    ‖fderiv ℝ (supportFlow σ hσ t) a v-
      polynomialPath (variationPolynomial a v N) (σ*t)‖≤‖v‖*(δ:ℝ) := by
  have hreg:=innerTube_flowTubeNeighborhood σ hσ ha universalStepCap_le_local
  have haball : a∈Metric.ball a (1/10000:ℝ) := Metric.mem_ball_self (by norm_num)
  have hs (s : ℝ) (hs : s∈Icc 0 (universalStepCap:ℝ)) : |σ*s|≤(universalStepCap:ℝ) := by
    rw [abs_mul,abs_of_nonneg hs.1]
    exact (mul_le_mul_of_nonneg_right hσ hs.1).trans (by simpa using hs.2)
  have hEXr : (0:ℝ)≤(EX:ℝ) := by exact_mod_cast hEX
  have hεVr : (0:ℝ)≤(εV:ℝ) := by exact_mod_cast hεV
  have h:=signedActualMixedVariationColumn_error σ hσ M N hreg haball
    (E:=(EX:ℝ)) (C:=‖v‖*(6/5)) (ε:=‖v‖*(εV:ℝ))
    universalStepCap_le_local hEXr (by positivity) (by positivity)
    (fun s h=>taylorPolynomial_order_tube ha hεX1 hstate hex (hs s h))
    (fun s h=>universal_signed_trueTaylor_order_error σ hσ ha
      hεX0 hεX1 hstate hex hstateBudget h)
    (fun s h=>variationPolynomial_order_uniform ha hN v hV (hs s h))
    (fun s h=>mixedVariationResidual_order_uniform ha hNM v hres (hs s h)) t ht
  have hb : 2*(4*(EX:ℝ)*(6/5)+(εV:ℝ))*(universalStepCap:ℝ)≤(δ:ℝ) := by
    have hh:=(Rat.cast_le (K:=ℝ)).mpr hbudget
    push_cast at hh
    exact hh
  apply h.trans
  calc
    _ = ‖v‖*(2*(4*(EX:ℝ)*(6/5)+(εV:ℝ))*t) := by ring
    _ ≤ ‖v‖*(2*(4*(EX:ℝ)*(6/5)+(εV:ℝ))*(universalStepCap:ℝ)) := by
      gcongr
      exact ht.2
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (norm_nonneg v)

theorem universal_signed_trueVariation42_22_error (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) (v : State) {t : ℝ}
    (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    ‖fderiv ℝ (supportFlow σ hσ t) a v-
      polynomialPath (variationPolynomial a v 22) (σ*t)‖≤‖v‖*((4:ℝ)/10^21) := by
  have h:=universal_signed_reducedVariation_error σ hσ ha (M:=42) (N:=22)
    (by omega) (by omega) v (εX:=(6:ℚ)/10^40) (EX:=(1:ℚ)/10^41)
    (εV:=(2:ℚ)/10^19) (δ:=(4:ℚ)/10^21)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    stateOrder42_budget.1.2 stateOrder42_budget.2 (by norm_num [universalStepCap])
    jacOrder22_budget.1.2 reducedJacobian_budgets.1 (by norm_num [universalStepCap]) ht
  norm_num at h ⊢
  exact h

theorem universal_signed_trueVariation44_22_error (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) (v : State) {t : ℝ}
    (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    ‖fderiv ℝ (supportFlow σ hσ t) a v-
      polynomialPath (variationPolynomial a v 22) (σ*t)‖≤‖v‖*((4:ℝ)/10^21) := by
  have h:=universal_signed_reducedVariation_error σ hσ ha (M:=44) (N:=22)
    (by omega) (by omega) v (εX:=(6:ℚ)/10^42) (EX:=(1:ℚ)/10^43)
    (εV:=(2:ℚ)/10^19) (δ:=(4:ℚ)/10^21)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    stateOrder44_budget.1.2 stateOrder44_budget.2 (by norm_num [universalStepCap])
    jacOrder22_budget.1.2 reducedJacobian_budgets.2 (by norm_num [universalStepCap]) ht
  norm_num at h ⊢
  exact h

theorem universal_signed_trueVariation42_22_operator_error (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) {t : ℝ} (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    ‖fderiv ℝ (supportFlow σ hσ t) a-variationPolynomialMap a 22 (σ*t)‖≤(4:ℝ)/10^21 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  simp only [sub_apply,variationPolynomialMap_apply]
  exact (universal_signed_trueVariation42_22_error σ hσ ha v ht).trans_eq (mul_comm _ _)

end
end SolitonClassification.Rotating.UniversalMajorant

#print axioms SolitonClassification.Rotating.UniversalMajorant.universal_signed_trueVariation42_22_operator_error
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Reduced state/variation actual error audit passed: {count} declarations; standard axioms only."
