import SolitonClassification.Rotating.UniversalVariationMajorantResidual
import SolitonClassification.Rotating.AnalyticMajorantBudget

/-! One exact rational budget for state degree60 and variation degree30.
The finite scalar residual is evaluated exactly once and then applies at
every inner-tube center and every initial direction, for both signs of time.
This is a polynomial residual bound, not yet an actual-flow Jacobian error. -/
namespace SolitonClassification.Rotating.UniversalMajorant
noncomputable section
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

def jacValue30 : ℚ :=
  ∑ n ∈ Finset.range 31,jacCoeff n*universalStepCap^n

def jacDerivative30 : ℚ :=
  ∑ n ∈ Finset.range 31,jacCoeff n*n*universalStepCap^(n-1)

def jacResidualValue6030 : ℚ :=
  3*(122/19)*scalarValue60^2*jacValue30-jacDerivative30

theorem jacValue30_bound : 0≤jacValue30 ∧ jacValue30≤6/5 := by
  decide +kernel

theorem jacResidualValue6030_bound :
    0≤jacResidualValue6030 ∧ jacResidualValue6030≤4/10^27 := by
  decide +kernel

lemma jacPolynomial30_value :
    (jacPolynomial 30).eval (universalStepCap:ℝ)=(jacValue30:ℝ) := by
  simp [jacPolynomial,jacValue30,eval_finsetSum]

lemma jacPolynomial30_derivative_value :
    (derivative (jacPolynomial 30)).eval (universalStepCap:ℝ)=(jacDerivative30:ℝ) := by
  simp [jacPolynomial,jacDerivative30,derivative_monomial,eval_finsetSum]

lemma jacResidual6030_value :
    (jacResidual 60 30).eval (universalStepCap:ℝ)=(jacResidualValue6030:ℝ) := by
  simp only [jacResidual,jacLipschitzPolynomial,eval_sub,eval_mul,eval_C,eval_pow,
    scalarPolynomial60_value,jacPolynomial30_value,jacPolynomial30_derivative_value]
  simp only [jacResidualValue6030,rate,Rat.cast_sub,Rat.cast_mul,Rat.cast_pow,
    Rat.cast_div,Rat.cast_ofNat]

theorem jacPolynomial30_uniform {t : ℝ} (ht : 0≤t) (hT : t≤(universalStepCap:ℝ)) :
    (jacPolynomial 30).eval t≤6/5 := by
  have h := eval_monotone_of_coeff_nonneg (jacPolynomial_nonneg 30) ht hT
  rw [jacPolynomial30_value] at h
  apply h.trans
  have hh := (Rat.cast_le (K:=ℝ)).mpr jacValue30_bound.2
  norm_num at hh ⊢
  exact hh

theorem jacResidual60_30_uniform {t : ℝ} (ht : 0≤t) (hT : t≤(universalStepCap:ℝ)) :
    0≤(jacResidual 60 30).eval t ∧ (jacResidual 60 30).eval t≤4/10^27 := by
  have hnonneg (n : ℕ) : 0≤(jacResidual 60 30).coeff n := jacResidual_nonneg 60 30 n (by omega)
  refine ⟨eval_nonneg_of_coeff_nonneg hnonneg ht,?_⟩
  have h := eval_monotone_of_coeff_nonneg hnonneg ht hT
  rw [jacResidual6030_value] at h
  apply h.trans
  have hh := (Rat.cast_le (K:=ℝ)).mpr jacResidualValue6030_bound.2
  norm_num at hh ⊢
  exact hh

theorem variationPolynomial30_uniform {a : State} (ha : a∈innerTube) (v : State)
    {t : ℝ} (hT : |t|≤(universalStepCap:ℝ)) :
    ‖polynomialPath (variationPolynomial a v 30) t‖≤‖v‖*(6/5) :=
  (variationPolynomial_norm_bound ha 60 30 (by omega) v t).trans
    (mul_le_mul_of_nonneg_left (jacPolynomial30_uniform (abs_nonneg t) hT) (norm_nonneg v))

theorem mixedVariationResidual60_30_uniform {a : State} (ha : a∈innerTube) (v : State)
    {t : ℝ} (hT : |t|≤(universalStepCap:ℝ)) :
    ‖polynomialPath (mixedVariationResidual a v 60 30) t‖≤‖v‖*(4/10^27) :=
  (mixedVariationResidual_norm_bound ha 60 30 (by omega) v t).trans
    (mul_le_mul_of_nonneg_left (jacResidual60_30_uniform (abs_nonneg t) hT).2 (norm_nonneg v))

/-- Actual derivative-field defect along the two specified polynomial paths.
An actual flow/Jacobian comparison and global propagation remain separate. -/
theorem actual_variation_residual60_30_uniform {a : State} (ha : a∈innerTube) (v : State)
    {t : ℝ} (hT : |t|≤(universalStepCap:ℝ)) :
    ‖polynomialVelocity (variationPolynomial a v 30) t-
      fderiv ℝ field (polynomialPath (taylorPolynomial a 60) t)
        (polynomialPath (variationPolynomial a v 30) t)‖≤‖v‖*(4/10^27) := by
  rw [←mixedVariationResidual_actual]
  exact mixedVariationResidual60_30_uniform ha v hT

end
end SolitonClassification.Rotating.UniversalMajorant

#print axioms SolitonClassification.Rotating.UniversalMajorant.actual_variation_residual60_30_uniform
open Lean Elab Command in
run_cmd do
  for (name, _) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
  logInfo "Universal variation degree60/30 budget audit passed; standard axioms only."
