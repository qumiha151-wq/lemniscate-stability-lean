import SolitonClassification.Rotating.AnalyticMajorantVectorActual
import SolitonClassification.Rotating.AnalyticMajorantBudget
import SolitonClassification.Rotating.ResidualODE

/-! The residual of the EXISTING finite Taylor polynomial is bounded at
every inner-tube center by one scalar residual. Finite algebra only:
no assumed analyticity, numerical residual, or coefficient enclosure. -/
namespace SolitonClassification.Rotating.UniversalMajorant
noncomputable section
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

lemma scalarForcing_high (N n : ℕ) (hn : N≤n) :
    (scalarForcing (displacementPolynomial N)).coeff n=(scalarResidual N).coeff n := by
  have hd : (derivative (displacementPolynomial N)).coeff n=0 := by
    rw [coeff_derivative,displacementPolynomial_pos N (n+1) (by omega),
      scalarPolynomial_coeff,if_neg (by omega),mul_zero,zero_mul]
  simp only [scalarForcing_eq,scalarResidual,coeff_sub,hd,sub_zero]

lemma actualPolynomialField_displaced (a : State) (N : ℕ) :
    polynomialField (taylorPolynomial a N)=
      displacedPolynomialField a (actualDisplacementPolynomial a N) := by
  rw [displacedPolynomialField_eq]
  congr 1
  funext i
  simp [actualDisplacementPolynomial]

theorem taylorResidual_coeff_majorized {a : State} (ha : a∈innerTube) (N n : ℕ) :
    ‖vectorPolynomialCoeff (taylorResidual a N) n‖≤(scalarResidual N).coeff n := by
  by_cases hn : n<N
  · have hz : vectorPolynomialCoeff (taylorResidual a N) n=0 := by
      funext i
      exact taylorResidual_low_zero a N n hn i
    rw [hz,norm_zero,scalarResidual_low N n hn]
  · have hd : ∀i,(derivative (taylorPolynomial a N i)).coeff n=0 := by
      intro i
      rw [coeff_derivative,taylorPolynomial_coeff,if_neg (by omega),zero_mul]
    have he : vectorPolynomialCoeff (taylorResidual a N) n=
        -vectorPolynomialCoeff (polynomialField (taylorPolynomial a N)) n := by
      funext i
      simp only [vectorPolynomialCoeff,taylorResidual,coeff_sub,hd,zero_sub,Pi.neg_apply]
    rw [he,norm_neg,actualPolynomialField_displaced,displacedPolynomialField_coeff,
      ←scalarForcing_high N n (by omega)]
    exact vectorTaylorRHS_bound ha N _ n
      (fun j _=>actualDisplacementPolynomial_coeff_majorized ha N j)

theorem taylorResidual_norm_bound {a : State} (ha : a∈innerTube) (N : ℕ) (t : ℝ) :
    ‖polynomialPath (taylorResidual a N) t‖≤(scalarResidual N).eval |t| :=
  vectorPolynomialEval_norm_le (taylorResidual a N) (scalarResidual N)
    (taylorResidual_coeff_majorized ha N) t

/-- One fixed scalar computation bounds the actual residual at EVERY
inner-tube center, for both positive and negative local times. -/
theorem taylorResidual60_uniform {a : State} (ha : a∈innerTube) {t : ℝ}
    (hT : |t|≤(universalStepCap:ℝ)) :
    ‖polynomialPath (taylorResidual a 60) t‖≤1/10^57 :=
  (taylorResidual_norm_bound ha 60 t).trans
    (scalarResidual60_uniform (abs_nonneg t) hT).2

theorem actual_velocity_residual60_uniform {a : State} (ha : a∈innerTube) {t : ℝ}
    (hT : |t|≤(universalStepCap:ℝ)) :
    ‖polynomialVelocity (taylorPolynomial a 60) t-
      field (polynomialPath (taylorPolynomial a 60) t)‖≤1/10^57 := by
  rw [←polynomial_residual_actual]
  exact taylorResidual60_uniform ha hT

end
end SolitonClassification.Rotating.UniversalMajorant

#print axioms SolitonClassification.Rotating.UniversalMajorant.taylorResidual_coeff_majorized
#print axioms SolitonClassification.Rotating.UniversalMajorant.taylorResidual60_uniform

open Lean Elab Command in
run_cmd do
  for (name, _) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Universal actual Taylor residual coefficients audited; standard axioms only."
