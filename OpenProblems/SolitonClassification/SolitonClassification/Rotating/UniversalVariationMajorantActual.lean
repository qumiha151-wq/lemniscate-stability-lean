import SolitonClassification.Rotating.UniversalVariationMajorantVector
import SolitonClassification.Rotating.VariationTaylor
import SolitonClassification.Rotating.FieldHessian

/-! The finite majorant bounds the PRE-EXISTING full six-state variationCoeff.
The bridge is proved by polynomial identities for the actual Frechet
derivative, including b and theta. No variational recurrence, coefficient
bound, actual-flow approximation, or infinite-series hypothesis is assumed. -/
namespace SolitonClassification.Rotating.UniversalMajorant
noncomputable section
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

lemma vectorPolynomialCoeff_smul (r : ℝ) (P : StatePolynomial) (n : ℕ) :
    vectorPolynomialCoeff (r • P) n=r • vectorPolynomialCoeff P n := by
  ext i
  simp [vectorPolynomialCoeff]

lemma vectorPolynomialEval_smul (r : ℝ) (P : StatePolynomial) (t : ℝ) :
    vectorPolynomialEval (r • P) t=r • vectorPolynomialEval P t := by
  ext i
  simp [vectorPolynomialEval,Polynomial.smul_eq_C_mul]

def displacedPolynomialVariation (a : State) (P W : StatePolynomial) : StatePolynomial :=
  polynomialLinear a W+polynomialBilinear a P W+polynomialBilinear a W P+
    (3:ℝ) • polynomialTrilinear P P W

lemma displacedPolynomialVariation_coeff (a : State) (P W : StatePolynomial) (n : ℕ) :
    vectorPolynomialCoeff (displacedPolynomialVariation a P W) n=
      variationTaylorRHS a (vectorPolynomialCoeff P) (vectorPolynomialCoeff W) n := by
  simp only [displacedPolynomialVariation,vectorPolynomialCoeff_add,vectorPolynomialCoeff_smul,
    polynomialLinear_coeff,polynomialBilinear_coeff,polynomialTrilinear_coeff,
    variationTaylorRHS,mixedBilinearCoeff,mixedTrilinearCoeff]

lemma displacedPolynomialVariation_eval (a : State) (P W : StatePolynomial) (t : ℝ) :
    vectorPolynomialEval (displacedPolynomialVariation a P W) t=
      linear (a+vectorPolynomialEval P t) (vectorPolynomialEval W t) := by
  simp only [displacedPolynomialVariation,vectorPolynomialEval_add,vectorPolynomialEval_smul,
    polynomialLinear_eval,polynomialBilinear_eval,polynomialTrilinear_eval]
  have h := linear_line_expansion a (vectorPolynomialEval P t) (vectorPolynomialEval W t) 1
  simpa only [one_smul,one_pow,add_assoc] using h.symm

lemma displacedPolynomialVariation_eq (a : State) (P W : StatePolynomial) :
    displacedPolynomialVariation a P W=polynomialVariation (fun i => C (a i)+P i) W := by
  funext i
  apply Polynomial.funext
  intro t
  have h1 := congrFun (displacedPolynomialVariation_eval a P W t) i
  have h2 := congrFun (polynomialVariation_eval (fun i => C (a i)+P i) W t) i
  simp only [field_fderiv_apply,eval_add,eval_C] at h2
  exact h1.trans h2.symm

/-- This is the actual original variationCoeff recurrence after the
constant state is separated; it is not an assumed or alternative recurrence. -/
theorem variationCoeff_displaced_recurrence (a v : State) (n : ℕ) :
    (n+1:ℝ) • variationCoeff a v (n+1)=
      variationTaylorRHS a (actualDisplacementCoeff a) (variationCoeff a v) n := by
  have hc : ∀ j≤n,vectorPolynomialCoeff (taylorPolynomial a n) j=taylorCoeff a j := by
    intro j hj
    funext i
    exact (taylorPolynomial_coeff a n j i).trans (if_pos hj)
  have hs : ∀ j≤n,squareCoeff (vectorPolynomialCoeff (taylorPolynomial a n)) j=
      squareCoeff (taylorCoeff a) j := by
    intro j hj
    apply squareCoeff_congr
    intro k hk
    exact hc k (by omega)
  have hw : ∀ j≤n,vectorPolynomialCoeff (variationPolynomial a v n) j=variationCoeff a v j := by
    intro j hj
    funext i
    exact (variationPolynomial_coeff a v n j i).trans (if_pos hj)
  have hactual := polynomialVariation_coeff (taylorPolynomial a n) (variationPolynomial a v n) n
  change vectorPolynomialCoeff (polynomialVariation (taylorPolynomial a n) (variationPolynomial a v n)) n=
    variationRHS (vectorPolynomialCoeff (taylorPolynomial a n))
      (squareCoeff (vectorPolynomialCoeff (taylorPolynomial a n)))
      (vectorPolynomialCoeff (variationPolynomial a v n)) n at hactual
  rw [variationRHS_congr _ _ _ _ _ _ n hc hs hw] at hactual
  have hd : ∀ j≤n,vectorPolynomialCoeff (actualDisplacementPolynomial a n) j=actualDisplacementCoeff a j := by
    intro j hj
    rw [actualDisplacementPolynomial_coeff,if_pos hj]
  have hshift : (fun i => C (a i)+actualDisplacementPolynomial a n i)=taylorPolynomial a n := by
    funext i
    simp [actualDisplacementPolynomial]
  have hp := displacedPolynomialVariation_coeff a (actualDisplacementPolynomial a n)
    (variationPolynomial a v n) n
  rw [displacedPolynomialVariation_eq,hshift,variationTaylorRHS_congr a _ _ _ _ n hd hw] at hp
  rw [variationCoeff_recurrence]
  exact hactual.symm.trans hp

/-- Main actual-coefficient result, allowing a higher state order M≥N and
an arbitrary actual initial variational direction v. -/
theorem variationCoeff_majorized {a : State} (ha : a∈innerTube)
    (M N : ℕ) (hNM : N≤M) (v : State) :
    ∀ n≤N,‖variationCoeff a v n‖≤‖v‖*(jacPolynomial N).coeff n :=
  variationTaylor_majorized ha M N hNM v (actualDisplacementCoeff a) (variationCoeff a v)
    (fun j hj => actualDisplacementCoeff_majorized ha M j (by omega))
    (variationCoeff_zero a v) (fun n _ => variationCoeff_displaced_recurrence a v n)

theorem variationPolynomial_coeff_majorized {a : State} (ha : a∈innerTube)
    (M N : ℕ) (hNM : N≤M) (v : State) (n : ℕ) :
    ‖vectorPolynomialCoeff (variationPolynomial a v N) n‖≤‖v‖*(jacPolynomial N).coeff n := by
  by_cases hn : n≤N
  · have he : vectorPolynomialCoeff (variationPolynomial a v N) n=variationCoeff a v n := by
      funext i
      exact (variationPolynomial_coeff a v N n i).trans (if_pos hn)
    rw [he]
    exact variationCoeff_majorized ha M N hNM v n hn
  · have he : vectorPolynomialCoeff (variationPolynomial a v N) n=0 := by
      funext i
      exact (variationPolynomial_coeff a v N n i).trans (if_neg hn)
    rw [he,norm_zero]
    exact mul_nonneg (norm_nonneg v) (jacPolynomial_nonneg N n)

/-- Signed-time bound for the existing finite variational polynomial. -/
theorem variationPolynomial_norm_bound {a : State} (ha : a∈innerTube)
    (M N : ℕ) (hNM : N≤M) (v : State) (t : ℝ) :
    ‖vectorPolynomialEval (variationPolynomial a v N) t‖≤‖v‖*(jacPolynomial N).eval |t| := by
  have h := vectorPolynomialEval_norm_le (variationPolynomial a v N) (C ‖v‖*jacPolynomial N)
    (fun n => by simpa only [coeff_C_mul] using variationPolynomial_coeff_majorized ha M N hNM v n) t
  simpa only [eval_mul,eval_C] using h

end
end SolitonClassification.Rotating.UniversalMajorant

#print axioms SolitonClassification.Rotating.UniversalMajorant.variationCoeff_displaced_recurrence
#print axioms SolitonClassification.Rotating.UniversalMajorant.variationCoeff_majorized
open Lean Elab Command in
run_cmd do
  for (name, _) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
  logInfo "Universal actual variation majorant audit passed; standard axioms only."
