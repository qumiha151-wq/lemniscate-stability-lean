import SolitonClassification.Rotating.UniversalVariationTrueTail

/-! Additional exact budgets at variation orders22 and20, with state order60.
The frozen order30 modules are unchanged. All true-flow comparisons use the
proved mixed-order theorem and retain its actual state-error forcing.
No numerical matrix benchmark or global P/Q bound is assumed here. -/
namespace SolitonClassification.Rotating.UniversalMajorant
noncomputable section
open Set Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

def jacValueAtCap (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range (N+1),jacCoeff n*universalStepCap^n

def jacDerivativeAtCap (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range (N+1),jacCoeff n*n*universalStepCap^(n-1)

def jacResidual60AtCap (N : ℕ) : ℚ :=
  3*(122/19)*scalarValue60^2*jacValueAtCap N-jacDerivativeAtCap N

theorem jacOrder22_budget :
    (0≤jacValueAtCap 22 ∧ jacValueAtCap 22≤6/5) ∧
      (0≤jacResidual60AtCap 22 ∧ jacResidual60AtCap 22≤2/10^19) := by
  decide +kernel

theorem jacOrder20_budget :
    (0≤jacValueAtCap 20 ∧ jacValueAtCap 20≤6/5) ∧
      (0≤jacResidual60AtCap 20 ∧ jacResidual60AtCap 20≤2/10^17) := by
  decide +kernel

lemma jacPolynomial_order_value (N : ℕ) :
    (jacPolynomial N).eval (universalStepCap:ℝ)=(jacValueAtCap N:ℝ) := by
  simp [jacPolynomial,jacValueAtCap,eval_finsetSum]

lemma jacPolynomial_order_derivative_value (N : ℕ) :
    (derivative (jacPolynomial N)).eval (universalStepCap:ℝ)=(jacDerivativeAtCap N:ℝ) := by
  simp [jacPolynomial,jacDerivativeAtCap,derivative_monomial,eval_finsetSum]

lemma jacResidual60_order_value (N : ℕ) :
    (jacResidual 60 N).eval (universalStepCap:ℝ)=(jacResidual60AtCap N:ℝ) := by
  simp only [jacResidual,jacLipschitzPolynomial,eval_sub,eval_mul,eval_C,eval_pow,
    scalarPolynomial60_value,jacPolynomial_order_value,jacPolynomial_order_derivative_value]
  simp only [jacResidual60AtCap,rate,Rat.cast_sub,Rat.cast_mul,Rat.cast_pow,
    Rat.cast_div,Rat.cast_ofNat]

theorem jacPolynomial_order_uniform {N : ℕ} (hb : jacValueAtCap N≤6/5)
    {t : ℝ} (ht : 0≤t) (hT : t≤(universalStepCap:ℝ)) :
    (jacPolynomial N).eval t≤6/5 := by
  have h := eval_monotone_of_coeff_nonneg (jacPolynomial_nonneg N) ht hT
  rw [jacPolynomial_order_value] at h
  apply h.trans
  have hh := (Rat.cast_le (K:=ℝ)).mpr hb
  norm_num at hh ⊢
  exact hh

theorem jacResidual60_order_uniform {N : ℕ} (hN : N≤60) {ε : ℚ}
    (hb : jacResidual60AtCap N≤ε) {t : ℝ} (ht : 0≤t) (hT : t≤(universalStepCap:ℝ)) :
    (jacResidual 60 N).eval t≤(ε:ℝ) := by
  have hn (n : ℕ) : 0≤(jacResidual 60 N).coeff n := jacResidual_nonneg 60 N n hN
  have h := eval_monotone_of_coeff_nonneg hn ht hT
  rw [jacResidual60_order_value] at h
  exact h.trans ((Rat.cast_le (K:=ℝ)).mpr hb)

theorem variationPolynomial_order_uniform {a : State} (ha : a∈innerTube)
    {N : ℕ} (hN : N≤60) (v : State) (hb : jacValueAtCap N≤6/5)
    {t : ℝ} (hT : |t|≤(universalStepCap:ℝ)) :
    ‖polynomialPath (variationPolynomial a v N) t‖≤‖v‖*(6/5) :=
  (variationPolynomial_norm_bound ha 60 N hN v t).trans
    (mul_le_mul_of_nonneg_left (jacPolynomial_order_uniform hb (abs_nonneg t) hT) (norm_nonneg v))

theorem mixedVariationResidual60_order_uniform {a : State} (ha : a∈innerTube)
    {N : ℕ} (hN : N≤60) (v : State) {ε : ℚ} (hb : jacResidual60AtCap N≤ε)
    {t : ℝ} (hT : |t|≤(universalStepCap:ℝ)) :
    ‖polynomialPath (mixedVariationResidual a v 60 N) t‖≤‖v‖*(ε:ℝ) :=
  (mixedVariationResidual_norm_bound ha 60 N hN v t).trans
    (mul_le_mul_of_nonneg_left (jacResidual60_order_uniform hN hb (abs_nonneg t) hT) (norm_nonneg v))

/-- A single finite rational budget closes all hypotheses of the mixed
actual-flow comparison. The interval and initial neighborhood are genuine. -/
theorem universal_signed_trueVariation_order_error (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) {N : ℕ} (hN : N≤60) (v : State)
    {ε δ : ℚ} (hε : 0≤ε) (hV : jacValueAtCap N≤6/5) (hR : jacResidual60AtCap N≤ε)
    (hbudget : 2*(4*((2:ℚ)/10^59)*(6/5)+ε)*universalStepCap≤δ)
    {t : ℝ} (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    ‖fderiv ℝ (supportFlow σ hσ t) a v-
      polynomialPath (variationPolynomial a v N) (σ*t)‖≤‖v‖*(δ:ℝ) := by
  have hreg : FlowTubeNeighborhood σ hσ (universalStepCap:ℝ) a (1/10000) :=
    innerTube_flowTubeNeighborhood σ hσ ha universalStepCap_le_local
  have haball : a∈Metric.ball a (1/10000:ℝ) := Metric.mem_ball_self (by norm_num)
  have hs (s : ℝ) (hs : s∈Icc 0 (universalStepCap:ℝ)) : |σ*s|≤(universalStepCap:ℝ) := by
    rw [abs_mul,abs_of_nonneg hs.1]
    exact (mul_le_mul_of_nonneg_right hσ hs.1).trans (by simpa using hs.2)
  have hεr : (0:ℝ)≤(ε:ℝ) := by exact_mod_cast hε
  have h := signedActualMixedVariationColumn_error σ hσ 60 N hreg haball
    (E:=(2:ℝ)/10^59) (C:=‖v‖*(6/5)) (ε:=‖v‖*(ε:ℝ))
    universalStepCap_le_local (by positivity) (by positivity) (by positivity)
    (fun s h => taylorPolynomial60_tube_uniform ha (hs s h))
    (fun s h => universal_signed_trueTaylor60_error_uniform σ hσ ha h)
    (fun s h => variationPolynomial_order_uniform ha hN v hV (hs s h))
    (fun s h => mixedVariationResidual60_order_uniform ha hN v hR (hs s h)) t ht
  have hbudgetr : 2*(4*((2:ℝ)/10^59)*(6/5)+(ε:ℝ))*(universalStepCap:ℝ)≤(δ:ℝ) := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr hbudget
    push_cast at hh
    exact hh
  apply h.trans
  calc
    _ = ‖v‖*(2*(4*((2:ℝ)/10^59)*(6/5)+(ε:ℝ))*t) := by ring
    _ ≤ ‖v‖*(2*(4*((2:ℝ)/10^59)*(6/5)+(ε:ℝ))*(universalStepCap:ℝ)) := by
      gcongr
      exact ht.2
    _ ≤ _ := mul_le_mul_of_nonneg_left hbudgetr (norm_nonneg v)

theorem variationPolynomial22_uniform {a : State} (ha : a∈innerTube) (v : State)
    {t : ℝ} (hT : |t|≤(universalStepCap:ℝ)) :
    ‖polynomialPath (variationPolynomial a v 22) t‖≤‖v‖*(6/5) :=
  variationPolynomial_order_uniform ha (by omega) v jacOrder22_budget.1.2 hT

theorem mixedVariationResidual60_22_uniform {a : State} (ha : a∈innerTube) (v : State)
    {t : ℝ} (hT : |t|≤(universalStepCap:ℝ)) :
    ‖polynomialPath (mixedVariationResidual a v 60 22) t‖≤‖v‖*((2:ℝ)/10^19) := by
  have h := mixedVariationResidual60_order_uniform ha (by omega) v jacOrder22_budget.2.2 hT
  norm_num at h ⊢
  exact h

theorem universal_signed_trueVariation60_22_error (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) (v : State) {t : ℝ}
    (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    ‖fderiv ℝ (supportFlow σ hσ t) a v-
      polynomialPath (variationPolynomial a v 22) (σ*t)‖≤‖v‖*((4:ℝ)/10^21) := by
  have h := universal_signed_trueVariation_order_error σ hσ ha (by omega) v
    (ε:=(2:ℚ)/10^19) (δ:=(4:ℚ)/10^21) (by norm_num)
    jacOrder22_budget.1.2 jacOrder22_budget.2.2 (by norm_num [universalStepCap]) ht
  norm_num at h ⊢
  exact h

theorem variationPolynomial20_uniform {a : State} (ha : a∈innerTube) (v : State)
    {t : ℝ} (hT : |t|≤(universalStepCap:ℝ)) :
    ‖polynomialPath (variationPolynomial a v 20) t‖≤‖v‖*(6/5) :=
  variationPolynomial_order_uniform ha (by omega) v jacOrder20_budget.1.2 hT

theorem mixedVariationResidual60_20_uniform {a : State} (ha : a∈innerTube) (v : State)
    {t : ℝ} (hT : |t|≤(universalStepCap:ℝ)) :
    ‖polynomialPath (mixedVariationResidual a v 60 20) t‖≤‖v‖*((2:ℝ)/10^17) := by
  have h := mixedVariationResidual60_order_uniform ha (by omega) v jacOrder20_budget.2.2 hT
  norm_num at h ⊢
  exact h

theorem universal_signed_trueVariation60_20_error (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) (v : State) {t : ℝ}
    (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    ‖fderiv ℝ (supportFlow σ hσ t) a v-
      polynomialPath (variationPolynomial a v 20) (σ*t)‖≤‖v‖*((4:ℝ)/10^19) := by
  have h := universal_signed_trueVariation_order_error σ hσ ha (by omega) v
    (ε:=(2:ℚ)/10^17) (δ:=(4:ℚ)/10^19) (by norm_num)
    jacOrder20_budget.1.2 jacOrder20_budget.2.2 (by norm_num [universalStepCap]) ht
  norm_num at h ⊢
  exact h

end
end SolitonClassification.Rotating.UniversalMajorant

#print axioms SolitonClassification.Rotating.UniversalMajorant.universal_signed_trueVariation60_22_error
#print axioms SolitonClassification.Rotating.UniversalMajorant.universal_signed_trueVariation60_20_error
open Lean Elab Command in
run_cmd do
  for (name, _) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
  logInfo "Universal order22/20 actual variation budget and tail audit passed; standard axioms only."
