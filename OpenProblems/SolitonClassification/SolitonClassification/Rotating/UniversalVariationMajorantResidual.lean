import SolitonClassification.Rotating.UniversalVariationMajorantActual

/-! Mixed-order finite variational residuals, for the pre-existing state
and variational polynomials. All coefficient bounds are conclusions.
This is the derivative-field residual along the polynomial state path;
it is not yet an actual-flow Jacobian truncation bound. -/
namespace SolitonClassification.Rotating.UniversalMajorant
noncomputable section
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

def mixedVariationResidual (a v : State) (M N : ℕ) : StatePolynomial := fun i =>
  derivative (variationPolynomial a v N i)-
    polynomialVariation (taylorPolynomial a M) (variationPolynomial a v N) i

lemma jacForcing_high (M N n : ℕ) (hn : N≤n) :
    (jacLipschitzPolynomial M*jacPolynomial N).coeff n=(jacResidual M N).coeff n := by
  have hd : (derivative (jacPolynomial N)).coeff n=0 := by
    rw [coeff_derivative,jacPolynomial_coeff,if_neg (by omega),zero_mul]
  simp only [jacResidual,coeff_sub,hd,sub_zero]

lemma actualPolynomialVariation_displaced (a v : State) (M N : ℕ) :
    polynomialVariation (taylorPolynomial a M) (variationPolynomial a v N)=
      displacedPolynomialVariation a (actualDisplacementPolynomial a M) (variationPolynomial a v N) := by
  rw [displacedPolynomialVariation_eq]
  congr 1
  funext i
  simp [actualDisplacementPolynomial]

theorem mixedVariationResidual_low_zero (a v : State) (M N n : ℕ)
    (hNM : N≤M) (hn : n<N) (i : Fin 6) : (mixedVariationResidual a v M N i).coeff n=0 := by
  have hc : ∀ j≤n,(fun i => (taylorPolynomial a M i).coeff j)=taylorCoeff a j := by
    intro j hj
    funext i
    rw [taylorPolynomial_coeff,if_pos (by omega)]
  have hq : ∀ j≤n,squareCoeff (fun j i => (taylorPolynomial a M i).coeff j) j=
      squareCoeff (taylorCoeff a) j := by
    intro j hj
    apply squareCoeff_congr
    intro k hk
    exact hc k (by omega)
  have hw : ∀ j≤n,(fun i => (variationPolynomial a v N i).coeff j)=variationCoeff a v j := by
    intro j hj
    funext i
    rw [variationPolynomial_coeff,if_pos (by omega)]
  have hr := congrFun (variationCoeff_recurrence a v n) i
  have hp := congrFun (polynomialVariation_coeff (taylorPolynomial a M) (variationPolynomial a v N) n) i
  rw [variationRHS_congr _ _ _ _ _ _ n hc hq hw] at hp
  simp only [mixedVariationResidual,coeff_sub,coeff_derivative,hp]
  rw [variationPolynomial_coeff,if_pos (by omega)]
  simpa only [Pi.smul_apply,smul_eq_mul,mul_comm] using sub_eq_zero.mpr hr

theorem mixedVariationResidual_coeff_majorized {a : State} (ha : a∈innerTube)
    (M N : ℕ) (hNM : N≤M) (v : State) (n : ℕ) :
    ‖vectorPolynomialCoeff (mixedVariationResidual a v M N) n‖≤‖v‖*(jacResidual M N).coeff n := by
  by_cases hn : n<N
  · have hz : vectorPolynomialCoeff (mixedVariationResidual a v M N) n=0 := by
      funext i
      exact mixedVariationResidual_low_zero a v M N n hNM hn i
    rw [hz,norm_zero,jacResidual_low M N n hNM hn,mul_zero]
  · have hd : ∀ i,(derivative (variationPolynomial a v N i)).coeff n=0 := by
      intro i
      rw [coeff_derivative,variationPolynomial_coeff,if_neg (by omega),zero_mul]
    have he : vectorPolynomialCoeff (mixedVariationResidual a v M N) n=
        -vectorPolynomialCoeff (polynomialVariation (taylorPolynomial a M) (variationPolynomial a v N)) n := by
      funext i
      simp only [vectorPolynomialCoeff,mixedVariationResidual,coeff_sub,hd,zero_sub,Pi.neg_apply]
    rw [he,norm_neg,actualPolynomialVariation_displaced,displacedPolynomialVariation_coeff,
      ←jacForcing_high M N n (by omega)]
    let q : ℝ[X] := C ‖v‖*jacPolynomial N
    have hq (j : ℕ) : 0≤q.coeff j := by
      change 0≤(C ‖v‖*jacPolynomial N).coeff j
      rw [coeff_C_mul]
      exact mul_nonneg (norm_nonneg v) (jacPolynomial_nonneg N j)
    have hb := variationTaylorRHS_bound ha M
      (vectorPolynomialCoeff (actualDisplacementPolynomial a M))
      (vectorPolynomialCoeff (variationPolynomial a v N)) q hq n
      (fun j _ => actualDisplacementPolynomial_coeff_majorized ha M j)
      (fun j _ => by simpa only [q,coeff_C_mul] using variationPolynomial_coeff_majorized ha M N hNM v j)
    have hmul : jacLipschitzPolynomial M*q=C ‖v‖*(jacLipschitzPolynomial M*jacPolynomial N) := by
      dsimp [q]
      ring
    rw [hmul,coeff_C_mul] at hb
    exact hb

theorem mixedVariationResidual_norm_bound {a : State} (ha : a∈innerTube)
    (M N : ℕ) (hNM : N≤M) (v : State) (t : ℝ) :
    ‖polynomialPath (mixedVariationResidual a v M N) t‖≤‖v‖*(jacResidual M N).eval |t| := by
  have h := vectorPolynomialEval_norm_le (mixedVariationResidual a v M N) (C ‖v‖*jacResidual M N)
    (fun n => by simpa only [coeff_C_mul] using mixedVariationResidual_coeff_majorized ha M N hNM v n) t
  rw [eval_mul,eval_C] at h
  exact h

theorem mixedVariationResidual_actual (a v : State) (M N : ℕ) (t : ℝ) :
    polynomialPath (mixedVariationResidual a v M N) t=
      polynomialVelocity (variationPolynomial a v N) t-
        fderiv ℝ field (polynomialPath (taylorPolynomial a M) t)
          (polynomialPath (variationPolynomial a v N) t) := by
  have h := polynomialVariation_eval (taylorPolynomial a M) (variationPolynomial a v N) t
  funext i
  have hi := congrFun h i
  change ((derivative (variationPolynomial a v N i))-
    polynomialVariation (taylorPolynomial a M) (variationPolynomial a v N) i).eval t=_
  rw [eval_sub,hi]
  rfl

end
end SolitonClassification.Rotating.UniversalMajorant

#print axioms SolitonClassification.Rotating.UniversalMajorant.mixedVariationResidual_coeff_majorized
#print axioms SolitonClassification.Rotating.UniversalMajorant.mixedVariationResidual_actual
open Lean Elab Command in
run_cmd do
  for (name, _) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
  logInfo "Universal mixed variation residual audit passed; standard axioms only."
