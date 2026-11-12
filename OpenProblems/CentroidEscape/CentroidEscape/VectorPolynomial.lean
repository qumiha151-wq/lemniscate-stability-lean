import CentroidEscape.VectorTaylor
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# The actual vector Taylor polynomial and its differential residual

The explicit polynomial lifts below identify the field coefficients with the
concrete convolution recurrence. Thus low residual coefficients cancel by
the constructed recurrence, while high coefficients are bounded by the
proved scalar residual. No residual or Taylor coefficient norm bound is an
input assumption. The final theorem also applies to the globally clipped
field when the center has the verified tube margin.
-/

namespace CentroidEscape
noncomputable section
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

abbrev VectorPolynomial := Fin 7 → ℝ[X]

def vectorPolynomialCoeff (P : VectorPolynomial) (n : ℕ) : WeightedState := fun i => (P i).coeff n
def vectorPolynomialEval (P : VectorPolynomial) (s : ℝ) : WeightedState := fun i => (P i).eval s

def polynomialLinear (a : WeightedState) (P : VectorPolynomial) : VectorPolynomial :=
  ![C 4*P 2,C 4*P 3,C (-16*a 4)*P 3+C (-16*a 3)*P 4,
    C (16*a 4)*P 2+C (16*a 2)*P 4,C 4*P 5,
    C (-96*(a 4)^2)*P 4+C (a 0/16)*P 3+C (a 3/16)*P 0-
      C (a 1/16)*P 2-C (a 2/16)*P 1,P 0]

def polynomialBilinear (a : WeightedState) (P Q : VectorPolynomial) : VectorPolynomial :=
  ![0,0,C (-16)*(P 4*Q 3),C 16*(P 4*Q 2),0,
    C (-96*a 4)*(P 4*Q 4)+C (1/16)*(P 0*Q 3-P 1*Q 2),0]

def polynomialTrilinear (P Q R : VectorPolynomial) : VectorPolynomial :=
  ![0,0,0,0,0,C (-32)*(P 4*(Q 4*R 4)),0]

lemma polynomialLinear_eval (a : WeightedState) (P : VectorPolynomial) (s : ℝ) :
    vectorPolynomialEval (polynomialLinear a P) s = weightedLinear a (vectorPolynomialEval P s) := by
  ext i
  fin_cases i <;> simp [vectorPolynomialEval, polynomialLinear, weightedLinear] <;> ring

lemma polynomialBilinear_eval (a : WeightedState) (P Q : VectorPolynomial) (s : ℝ) :
    vectorPolynomialEval (polynomialBilinear a P Q) s =
      weightedBilinear a (vectorPolynomialEval P s) (vectorPolynomialEval Q s) := by
  ext i
  fin_cases i <;> simp [vectorPolynomialEval, polynomialBilinear, weightedBilinear] <;> ring

lemma polynomialTrilinear_eval (P Q R : VectorPolynomial) (s : ℝ) :
    vectorPolynomialEval (polynomialTrilinear P Q R) s =
      weightedTrilinear (vectorPolynomialEval P s) (vectorPolynomialEval Q s) (vectorPolynomialEval R s) := by
  ext i
  fin_cases i <;> simp [vectorPolynomialEval, polynomialTrilinear, weightedTrilinear]
  all_goals ring

lemma polynomialLinear_coeff (a : WeightedState) (P : VectorPolynomial) (n : ℕ) :
    vectorPolynomialCoeff (polynomialLinear a P) n = weightedLinear a (vectorPolynomialCoeff P n) := by
  ext i
  fin_cases i <;> dsimp only [vectorPolynomialCoeff, polynomialLinear, weightedLinear]
  all_goals try simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', coeff_C_mul, coeff_add, coeff_sub]
  all_goals ring

lemma polynomialBilinear_coeff (a : WeightedState) (P Q : VectorPolynomial) (n : ℕ) :
    vectorPolynomialCoeff (polynomialBilinear a P Q) n =
      ∑ ij ∈ Finset.antidiagonal n, weightedBilinear a (vectorPolynomialCoeff P ij.1)
        (vectorPolynomialCoeff Q ij.2) := by
  ext i
  fin_cases i <;> simp only [Finset.sum_apply] <;>
    dsimp only [vectorPolynomialCoeff, polynomialBilinear, weightedBilinear]
  all_goals try simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', coeff_C_mul, coeff_add, coeff_sub, coeff_zero]
  all_goals try simp only [coeff_mul, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_const_zero, mul_assoc]
  all_goals ring_nf
  all_goals simp only [Finset.sum_add_distrib, Finset.sum_mul, add_assoc]

lemma polynomialTrilinear_coeff (P Q R : VectorPolynomial) (n : ℕ) :
    vectorPolynomialCoeff (polynomialTrilinear P Q R) n =
      ∑ ij ∈ Finset.antidiagonal n, ∑ jk ∈ Finset.antidiagonal ij.2,
        weightedTrilinear (vectorPolynomialCoeff P ij.1) (vectorPolynomialCoeff Q jk.1)
          (vectorPolynomialCoeff R jk.2) := by
  ext i
  fin_cases i <;> simp only [Finset.sum_apply] <;>
    dsimp only [vectorPolynomialCoeff, polynomialTrilinear, weightedTrilinear]
  all_goals try simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', coeff_C_mul, coeff_zero]
  all_goals try simp only [coeff_mul, Finset.mul_sum, Finset.sum_const_zero, mul_assoc]

def constantVectorPolynomial (z : WeightedState) : VectorPolynomial := fun i => C (z i)

def polynomialField (a : WeightedState) (P : VectorPolynomial) : VectorPolynomial :=
  constantVectorPolynomial (weightedField a) + polynomialLinear a P +
    polynomialBilinear a P P + polynomialTrilinear P P P

lemma vectorPolynomialEval_add (P Q : VectorPolynomial) (s : ℝ) :
    vectorPolynomialEval (P+Q) s = vectorPolynomialEval P s + vectorPolynomialEval Q s := by
  ext i
  simp [vectorPolynomialEval]

lemma vectorPolynomialCoeff_add (P Q : VectorPolynomial) (n : ℕ) :
    vectorPolynomialCoeff (P+Q) n = vectorPolynomialCoeff P n + vectorPolynomialCoeff Q n := by
  ext i
  simp [vectorPolynomialCoeff]

lemma constantVectorPolynomial_eval (z : WeightedState) (s : ℝ) :
    vectorPolynomialEval (constantVectorPolynomial z) s = z := by
  ext i
  simp [vectorPolynomialEval, constantVectorPolynomial]

lemma constantVectorPolynomial_coeff (z : WeightedState) (n : ℕ) :
    vectorPolynomialCoeff (constantVectorPolynomial z) n = if n=0 then z else 0 := by
  ext i
  by_cases h : n=0 <;> simp [vectorPolynomialCoeff, constantVectorPolynomial, coeff_C, h]

lemma polynomialField_eval (a : WeightedState) (P : VectorPolynomial) (s : ℝ) :
    vectorPolynomialEval (polynomialField a P) s = weightedField (a+vectorPolynomialEval P s) := by
  simp only [polynomialField, vectorPolynomialEval_add, constantVectorPolynomial_eval,
    polynomialLinear_eval, polynomialBilinear_eval, polynomialTrilinear_eval,
    weightedField_expansion]

lemma polynomialField_coeff (a : WeightedState) (P : VectorPolynomial) (n : ℕ) :
    vectorPolynomialCoeff (polynomialField a P) n = vectorTaylorRHS a (vectorPolynomialCoeff P) n := by
  simp only [polynomialField, vectorPolynomialCoeff_add, constantVectorPolynomial_coeff,
    polynomialLinear_coeff, polynomialBilinear_coeff, polynomialTrilinear_coeff,
    vectorTaylorRHS, quadraticTaylorCoeff, cubicTaylorCoeff]

def canonicalDisplacementPolynomial (a : WeightedState) : VectorPolynomial :=
  fun i => ∑ n ∈ Finset.range 161, monomial n (canonicalTaylorCoeff a n i)

lemma canonicalDisplacementPolynomial_coeff (a : WeightedState) (n : ℕ) :
    vectorPolynomialCoeff (canonicalDisplacementPolynomial a) n =
      if n<161 then canonicalTaylorCoeff a n else 0 := by
  ext i
  simp only [vectorPolynomialCoeff, canonicalDisplacementPolynomial, finsetSum_coeff,
    coeff_monomial]
  by_cases hn : n<161 <;> simp [Finset.mem_range, eq_comm, hn]

lemma canonicalDisplacementPolynomial_eval (a : WeightedState) (t : ℝ) :
    vectorPolynomialEval (canonicalDisplacementPolynomial a) t = canonicalTaylorPolynomial a t-a := by
  ext i
  simp only [vectorPolynomialEval, canonicalDisplacementPolynomial, eval_finsetSum,
    eval_monomial, canonicalTaylorPolynomial, Pi.add_apply, Pi.sub_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  simp only [add_sub_cancel_left, mul_comm]

def vectorPolynomialDerivative (P : VectorPolynomial) : VectorPolynomial := fun i => derivative (P i)

lemma vectorPolynomialDerivative_coeff (P : VectorPolynomial) (n : ℕ) :
    vectorPolynomialCoeff (vectorPolynomialDerivative P) n =
      (n+1:ℝ) • vectorPolynomialCoeff P (n+1) := by
  ext i
  simp only [vectorPolynomialCoeff, vectorPolynomialDerivative, coeff_derivative,
    Pi.smul_apply, smul_eq_mul]
  ring

lemma canonicalDisplacementPolynomial_derivative_eval (a : WeightedState) (t : ℝ) :
    vectorPolynomialEval (vectorPolynomialDerivative (canonicalDisplacementPolynomial a)) t =
      canonicalTaylorDerivative a t := by
  ext i
  simp only [vectorPolynomialEval, vectorPolynomialDerivative, canonicalDisplacementPolynomial,
    derivative_sum, derivative_monomial, eval_finsetSum, eval_monomial,
    canonicalTaylorDerivative, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro n hn
  ring

lemma canonicalDisplacementPolynomial_coeff_majorized {a : WeightedState} (ha : a ∈ weightedTube)
    (n : ℕ) :
    ‖vectorPolynomialCoeff (canonicalDisplacementPolynomial a) n‖ ≤ displacementMajorant.coeff n := by
  rw [canonicalDisplacementPolynomial_coeff]
  split_ifs with hn
  · exact canonicalTaylorCoeff_majorized ha n (by omega)
  · simp only [norm_zero]
    exact displacementMajorant_nonneg n

def canonicalResidualPolynomial (a : WeightedState) : VectorPolynomial :=
  vectorPolynomialDerivative (canonicalDisplacementPolynomial a)-
    polynomialField a (canonicalDisplacementPolynomial a)

lemma vectorPolynomialCoeff_sub (P Q : VectorPolynomial) (n : ℕ) :
    vectorPolynomialCoeff (P-Q) n = vectorPolynomialCoeff P n-vectorPolynomialCoeff Q n := by
  ext i
  simp [vectorPolynomialCoeff]

lemma vectorPolynomialEval_sub (P Q : VectorPolynomial) (s : ℝ) :
    vectorPolynomialEval (P-Q) s = vectorPolynomialEval P s-vectorPolynomialEval Q s := by
  ext i
  simp [vectorPolynomialEval]

lemma canonicalResidualPolynomial_eval (a : WeightedState) (t : ℝ) :
    vectorPolynomialEval (canonicalResidualPolynomial a) t =
      canonicalTaylorDerivative a t-weightedField (canonicalTaylorPolynomial a t) := by
  rw [canonicalResidualPolynomial, vectorPolynomialEval_sub,
    canonicalDisplacementPolynomial_derivative_eval, polynomialField_eval,
    canonicalDisplacementPolynomial_eval, add_sub_cancel]

lemma canonicalResidualPolynomial_coeff_low (a : WeightedState) (n : ℕ) (hn : n<160) :
    vectorPolynomialCoeff (canonicalResidualPolynomial a) n = 0 := by
  rw [canonicalResidualPolynomial, vectorPolynomialCoeff_sub, vectorPolynomialDerivative_coeff,
    canonicalDisplacementPolynomial_coeff, if_pos (by omega), polynomialField_coeff]
  have he := vectorTaylorRHS_congr a (vectorPolynomialCoeff (canonicalDisplacementPolynomial a))
    (canonicalTaylorCoeff a) n (by
      intro j hj
      rw [canonicalDisplacementPolynomial_coeff, if_pos (by omega)])
  rw [he, canonicalTaylorCoeff_recurrence, sub_self]

lemma scalarForcing_coeff_high (n : ℕ) (hn : 160 ≤ n) :
    scalarForcing.coeff n = scalarResidual.coeff n := by
  have hd : (derivative scalarMajorant).coeff n = 0 := by
    rw [coeff_derivative, scalarMajorant_coeff, if_neg (by omega), zero_mul]
  simp only [scalarForcing_eq, scalarResidual, coeff_sub, coeff_C_mul, hd, mul_zero, sub_zero]

theorem canonicalResidualPolynomial_coeff_bound {a : WeightedState} (ha : a ∈ weightedTube)
    (n : ℕ) :
    ‖vectorPolynomialCoeff (canonicalResidualPolynomial a) n‖ ≤ scalarResidual.coeff n := by
  by_cases hn : n<160
  · rw [canonicalResidualPolynomial_coeff_low a n hn, norm_zero,
      scalarResidual_low_coeff_zero n hn]
  · rw [canonicalResidualPolynomial, vectorPolynomialCoeff_sub, vectorPolynomialDerivative_coeff,
      canonicalDisplacementPolynomial_coeff, if_neg (by omega), smul_zero, zero_sub, norm_neg,
      polynomialField_coeff, ← scalarForcing_coeff_high n (by omega)]
    exact vectorTaylorRHS_bound ha _ n (fun j _ => canonicalDisplacementPolynomial_coeff_majorized ha j)

lemma abs_eval_le_of_coeff_bound {p q : ℝ[X]} (h : ∀ n, |p.coeff n| ≤ q.coeff n)
    {t : ℝ} (ht : 0 ≤ t) : |p.eval t| ≤ q.eval t := by
  let N := max p.natDegree q.natDegree+1
  have hp : p.natDegree<N := by dsimp [N]; omega
  have hq : q.natDegree<N := by dsimp [N]; omega
  rw [eval_eq_sum_range' hp, eval_eq_sum_range' hq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [abs_mul, abs_of_nonneg (pow_nonneg ht n)]
  exact mul_le_mul_of_nonneg_right (h n) (pow_nonneg ht n)

lemma vectorPolynomialEval_norm_bound {P : VectorPolynomial} {q : ℝ[X]}
    (h : ∀ n, ‖vectorPolynomialCoeff P n‖ ≤ q.coeff n)
    {t : ℝ} (ht : 0 ≤ t) : ‖vectorPolynomialEval P t‖ ≤ q.eval t := by
  have hq : 0 ≤ q.eval t := eval_nonneg_of_coeff_nonneg
    (fun n => (norm_nonneg _).trans (h n)) ht
  apply (pi_norm_le_iff_of_nonneg hq).mpr
  intro i
  simp only [vectorPolynomialEval, Real.norm_eq_abs]
  apply abs_eval_le_of_coeff_bound _ ht
  intro n
  have hi : |(P i).coeff n| ≤ ‖vectorPolynomialCoeff P n‖ := by
    simpa only [vectorPolynomialCoeff, Real.norm_eq_abs] using
      norm_le_pi_norm (vectorPolynomialCoeff P n) i
  exact hi.trans (h n)

theorem canonicalTaylorPolynomial_residual_bound {a : WeightedState} (ha : a ∈ weightedTube)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖canonicalTaylorDerivative a t-weightedField (canonicalTaylorPolynomial a t)‖ ≤
      scalarResidual.eval t := by
  rw [← canonicalResidualPolynomial_eval]
  exact vectorPolynomialEval_norm_bound (canonicalResidualPolynomial_coeff_bound ha) ht

theorem canonicalTaylorPolynomial_residual_uniform {a : WeightedState} (ha : a ∈ weightedTube)
    {t : ℝ} (ht : 0 ≤ t) (htmax : t ≤ 1/100) :
    ‖canonicalTaylorDerivative a t-weightedField (canonicalTaylorPolynomial a t)‖ ≤
      (polynomialResidual:ℝ) := by
  apply (canonicalTaylorPolynomial_residual_bound ha ht).trans
  rw [← scalarResidual_value]
  exact (scalarResidual_bounds ht htmax).2

theorem canonicalTaylorPolynomial_deriv_residual_uniform {a : WeightedState} (ha : a ∈ weightedTube)
    {t : ℝ} (ht : 0 ≤ t) (htmax : t ≤ 1/100) :
    ‖deriv (canonicalTaylorPolynomial a) t-weightedField (canonicalTaylorPolynomial a t)‖ ≤
      (polynomialResidual:ℝ) := by
  rw [(canonicalTaylorPolynomial_hasDerivAt a t).deriv]
  exact canonicalTaylorPolynomial_residual_uniform ha ht htmax

theorem canonicalTaylorPolynomial_clipped_residual_uniform {a : WeightedState}
    (ha : ∀ i : Fin 7, i ≠ 6 → |a i| ≤ tubeRadius i-23/1000)
    {t : ℝ} (ht : 0 ≤ t) (htmax : t ≤ 1/100) :
    ‖deriv (canonicalTaylorPolynomial a) t-clippedField (canonicalTaylorPolynomial a t)‖ ≤
      (polynomialResidual:ℝ) := by
  rw [clippedField_eq (canonicalTaylorPolynomial_in_tube ha ht htmax)]
  apply canonicalTaylorPolynomial_deriv_residual_uniform _ ht htmax
  intro i hi
  linarith [ha i hi]

end
end CentroidEscape

#print axioms CentroidEscape.canonicalTaylorPolynomial_deriv_residual_uniform
#print axioms CentroidEscape.canonicalTaylorPolynomial_clipped_residual_uniform

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Vector-polynomial audit passed for {checked} declarations."


