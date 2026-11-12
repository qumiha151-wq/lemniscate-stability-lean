import SolitonClassification.Rotating.UniversalTrueStateTail

/-! Exact finite budgets at lower state orders. This extends the frozen
order60 theory without changing its definitions or candidate certificate.
No concrete many-segment reference grid is asserted here. -/
namespace SolitonClassification.Rotating.UniversalMajorant
noncomputable section
open Set Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

def stateScalarValueAtCap (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range (N+1),scalarCoeff n*universalStepCap^n

def stateScalarDerivativeAtCap (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range (N+1),scalarCoeff n*n*universalStepCap^(n-1)

def stateResidualAtCap (N : ℕ) : ℚ :=
  61*(stateScalarValueAtCap N)^3-(19/2)*stateScalarDerivativeAtCap N

theorem stateOrder42_budget :
    (0≤stateResidualAtCap 42 ∧ stateResidualAtCap 42≤6/10^40) ∧
      (19/2)*(stateScalarValueAtCap 42-1)≤129/250 := by
  decide +kernel

theorem stateOrder44_budget :
    (0≤stateResidualAtCap 44 ∧ stateResidualAtCap 44≤6/10^42) ∧
      (19/2)*(stateScalarValueAtCap 44-1)≤129/250 := by
  decide +kernel

lemma scalarPolynomial_order_value (N : ℕ) :
    (scalarPolynomial N).eval (universalStepCap:ℝ)=(stateScalarValueAtCap N:ℝ) := by
  simp [scalarPolynomial,stateScalarValueAtCap,eval_finsetSum]

lemma scalarPolynomial_order_derivative_value (N : ℕ) :
    (derivative (scalarPolynomial N)).eval (universalStepCap:ℝ)=
      (stateScalarDerivativeAtCap N:ℝ) := by
  simp [scalarPolynomial,stateScalarDerivativeAtCap,derivative_monomial,eval_finsetSum]

lemma scalarResidual_order_value (N : ℕ) :
    (scalarResidual N).eval (universalStepCap:ℝ)=(stateResidualAtCap N:ℝ) := by
  simp only [scalarResidual,displacementPolynomial,derivative_mul,derivative_sub,
    derivative_C,derivative_one,zero_mul,zero_add,sub_zero,eval_sub,eval_mul,
    eval_C,eval_pow,scalarPolynomial_order_value,scalarPolynomial_order_derivative_value]
  simp only [stateResidualAtCap,Rat.cast_sub,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,
    Rat.cast_ofNat]

theorem stateResidual_order_uniform {N : ℕ} {ε : ℚ}
    (hb : stateResidualAtCap N≤ε) {t : ℝ} (ht : 0≤t)
    (hT : t≤(universalStepCap:ℝ)) : (scalarResidual N).eval t≤(ε:ℝ) := by
  have h:=(scalarResidual_uniform N ht hT).2
  rw [scalarResidual_order_value] at h
  exact h.trans ((Rat.cast_le (K:=ℝ)).mpr hb)

theorem stateDisplacement_order_uniform {N : ℕ}
    (hb : (19/2)*(stateScalarValueAtCap N-1)≤129/250)
    {t : ℝ} (ht : 0≤t) (hT : t≤(universalStepCap:ℝ)) :
    (displacementPolynomial N).eval t≤129/250 := by
  have h:=eval_monotone_of_coeff_nonneg (displacementPolynomial_nonneg N) ht hT
  apply h.trans
  simp only [displacementPolynomial,eval_mul,eval_C,eval_sub,eval_one,scalarPolynomial_order_value]
  have hh:=(Rat.cast_le (K:=ℝ)).mpr hb
  push_cast at hh ⊢
  exact hh

theorem taylorResidual_order_uniform {a : State} (ha : a∈innerTube)
    {N : ℕ} {ε : ℚ} (hb : stateResidualAtCap N≤ε) {t : ℝ}
    (hT : |t|≤(universalStepCap:ℝ)) :
    ‖polynomialPath (taylorResidual a N) t‖≤(ε:ℝ) :=
  (taylorResidual_norm_bound ha N t).trans
    (stateResidual_order_uniform hb (abs_nonneg t) hT)

theorem taylorPolynomial_order_tube {a : State} (ha : a∈innerTube)
    {N : ℕ} {ε : ℚ} (hε : ε≤1) (hb : stateResidualAtCap N≤ε)
    (hex : (19/2)*(stateScalarValueAtCap N-1)≤129/250) {t : ℝ}
    (hT : |t|≤(universalStepCap:ℝ)) :
    polynomialPath (taylorPolynomial a N) t∈outerTube := by
  apply taylorPolynomial_tube_of_coarse_excursion ha N universalStepCap_pos.le universalStepCap_le_local
    (fun s hs => (taylorPolynomial_excursion ha N s).trans
      (stateDisplacement_order_uniform hex (abs_nonneg s) hs)) _ hT
  intro s hs
  exact (taylorResidual_order_uniform ha hb hs).trans (by exact_mod_cast hε)

theorem universal_signed_trueTaylor_order_error (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) {N : ℕ} {ε δ : ℚ}
    (hε0 : 0≤ε) (hε1 : ε≤1) (hres : stateResidualAtCap N≤ε)
    (hex : (19/2)*(stateScalarValueAtCap N-1)≤129/250)
    (hbudget : 2*ε*universalStepCap≤δ) {t : ℝ}
    (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    ‖supportFlow σ hσ t a-polynomialPath (taylorPolynomial a N) (σ*t)‖≤(δ:ℝ) := by
  have hεr : (0:ℝ)≤(ε:ℝ) := by exact_mod_cast hε0
  have hs (s : ℝ) (hs : s∈Icc 0 (universalStepCap:ℝ)) : |σ*s|≤(universalStepCap:ℝ) := by
    rw [abs_mul,abs_of_nonneg hs.1]
    exact (mul_le_mul_of_nonneg_right hσ hs.1).trans (by simpa using hs.2)
  have h:=signedTrueTaylorSegment_error σ hσ ha N universalStepCap_le_local hεr
    (fun s h => taylorPolynomial_order_tube ha hε1 hres hex (hs s h))
    (fun s h => taylorResidual_order_uniform ha hres (hs s h)) t ht
  apply h.trans
  apply (mul_le_mul_of_nonneg_left ht.2 (by positivity : 0≤2*(ε:ℝ))).trans
  have hb:=(Rat.cast_le (K:=ℝ)).mpr hbudget
  push_cast at hb
  exact hb

theorem taylorResidual42_uniform {a : State} (ha : a∈innerTube) {t : ℝ}
    (ht : |t|≤(universalStepCap:ℝ)) :
    ‖polynomialPath (taylorResidual a 42) t‖≤(6:ℝ)/10^40 := by
  have h:=taylorResidual_order_uniform ha stateOrder42_budget.1.2 ht
  norm_num at h ⊢
  exact h

theorem taylorResidual44_uniform {a : State} (ha : a∈innerTube) {t : ℝ}
    (ht : |t|≤(universalStepCap:ℝ)) :
    ‖polynomialPath (taylorResidual a 44) t‖≤(6:ℝ)/10^42 := by
  have h:=taylorResidual_order_uniform ha stateOrder44_budget.1.2 ht
  norm_num at h ⊢
  exact h

theorem universal_signed_trueTaylor42_error (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) {t : ℝ} (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    ‖supportFlow σ hσ t a-polynomialPath (taylorPolynomial a 42) (σ*t)‖≤(1:ℝ)/10^41 := by
  have h:=universal_signed_trueTaylor_order_error σ hσ ha (N:=42)
    (ε:=(6:ℚ)/10^40) (δ:=(1:ℚ)/10^41) (by norm_num) (by norm_num)
    stateOrder42_budget.1.2 stateOrder42_budget.2 (by norm_num [universalStepCap]) ht
  norm_num at h ⊢
  exact h

theorem universal_signed_trueTaylor44_error (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) {t : ℝ} (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    ‖supportFlow σ hσ t a-polynomialPath (taylorPolynomial a 44) (σ*t)‖≤(1:ℝ)/10^43 := by
  have h:=universal_signed_trueTaylor_order_error σ hσ ha (N:=44)
    (ε:=(6:ℚ)/10^42) (δ:=(1:ℚ)/10^43) (by norm_num) (by norm_num)
    stateOrder44_budget.1.2 stateOrder44_budget.2 (by norm_num [universalStepCap]) ht
  norm_num at h ⊢
  exact h

end
end SolitonClassification.Rotating.UniversalMajorant

#print axioms SolitonClassification.Rotating.UniversalMajorant.universal_signed_trueTaylor42_error
#print axioms SolitonClassification.Rotating.UniversalMajorant.universal_signed_trueTaylor44_error
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Universal lower-state-order actual tails audited: {count} declarations; standard axioms only."
