import CentroidEscape.OrderScalarResidual

/-! Actual finite vector residual majorization at arbitrary N<=160. -/
namespace CentroidEscape.MetricStability
noncomputable section
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

lemma quadraticTaylorCoeff_bound_poly {a : WeightedState} (ha : a ∈ weightedTube)
    (w : ℝ[X]) (hw : ∀ j, 0≤w.coeff j)
    (p : ℕ → WeightedState) (n : ℕ)
    (hp : ∀ j ≤ n, ‖p j‖ ≤ w.coeff j) :
    ‖quadraticTaylorCoeff a p n‖ ≤ 22*(w^2).coeff n := by
  rw [quadraticTaylorCoeff, pow_two, coeff_mul, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ij hij
  have he := Finset.mem_antidiagonal.mp hij
  have hwi := hw ij.1
  have hwj := hw ij.2
  calc
    _ ≤ 22*‖p ij.1‖*‖p ij.2‖ := weightedBilinear_bound ha _ _
    _ ≤ 22*w.coeff ij.1*w.coeff ij.2 := by
      gcongr <;> apply hp <;> omega
    _ = _ := by ring

lemma cubicTaylorCoeff_bound_poly (w : ℝ[X]) (hw : ∀ j, 0≤w.coeff j)
    (p : ℕ → WeightedState) (n : ℕ)
    (hp : ∀ j ≤ n, ‖p j‖ ≤ w.coeff j) :
    ‖cubicTaylorCoeff p n‖ ≤ 32*(w^3).coeff n := by
  have heq : w^3 = w*(w*w) := by ring
  rw [cubicTaylorCoeff, heq, coeff_mul, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ij hij
  have he := Finset.mem_antidiagonal.mp hij
  rw [coeff_mul, Finset.mul_sum, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro jk hjk
  have hj := Finset.mem_antidiagonal.mp hjk
  have hwi := hw ij.1
  have hwj := hw jk.1
  have hwk := hw jk.2
  calc
    _ ≤ 32*‖p ij.1‖*‖p jk.1‖*‖p jk.2‖ := weightedTrilinear_bound _ _ _
    _ ≤ 32*w.coeff ij.1*w.coeff jk.1*w.coeff jk.2 := by
      gcongr <;> apply hp <;> omega
    _ = _ := by ring

lemma vectorTaylorRHS_bound_poly {a : WeightedState} (ha : a ∈ weightedTube)
    (w : ℝ[X]) (hw : ∀ j, 0≤w.coeff j)
    (p : ℕ → WeightedState) (n : ℕ)
    (hp : ∀ j ≤ n, ‖p j‖ ≤ w.coeff j) :
    ‖vectorTaylorRHS a p n‖ ≤ (forcingPolynomial w).coeff n := by
  have hzero : ‖if n = 0 then weightedField a else 0‖ ≤ (C 2 : ℝ[X]).coeff n := by
    by_cases hn : n = 0
    · subst n
      simpa using weightedField_bound ha
    · simp [hn, coeff_C]
  have hl : ‖weightedLinear a (p n)‖ ≤ 8*w.coeff n :=
    (weightedLinear_bound ha _).trans (mul_le_mul_of_nonneg_left (hp n le_rfl) (by norm_num))
  have hq := quadraticTaylorCoeff_bound_poly ha w hw p n hp
  have hc := cubicTaylorCoeff_bound_poly w hw p n hp
  have hwn := hw n
  have hw2 : 0 ≤ (w^2).coeff n := by
    rw [pow_two]
    exact coeff_mul_nonneg_all hw hw n
  have hw3 : 0 ≤ (w^3).coeff n := by
    have h := coeff_mul_nonneg_all
      (coeff_mul_nonneg_all hw hw)
      hw n
    convert h using 1
    congr 1
    ring
  have h1 := norm_add_le (if n = 0 then weightedField a else 0) (weightedLinear a (p n))
  have h2 := norm_add_le ((if n = 0 then weightedField a else 0)+weightedLinear a (p n))
    (quadraticTaylorCoeff a p n)
  have h3 := norm_add_le ((if n = 0 then weightedField a else 0)+weightedLinear a (p n)+
    quadraticTaylorCoeff a p n) (cubicTaylorCoeff p n)
  simp only [vectorTaylorRHS, forcingPolynomial, coeff_add, coeff_C_mul]
  linarith


def orderDisplacementPolynomial (N : ℕ) (a : WeightedState) : VectorPolynomial :=
  fun i=>∑ n ∈ Finset.range (N+1), monomial n (canonicalTaylorCoeff a n i)

lemma orderDisplacementPolynomial_coeff (N : ℕ) (a : WeightedState) (n : ℕ) :
    vectorPolynomialCoeff (orderDisplacementPolynomial N a) n=
      if n<N+1 then canonicalTaylorCoeff a n else 0 := by
  ext i
  simp only [vectorPolynomialCoeff,orderDisplacementPolynomial,finsetSum_coeff,coeff_monomial]
  by_cases hn : n<N+1 <;> simp [Finset.mem_range,eq_comm,hn]

lemma orderDisplacementPolynomial_eval {N : ℕ} (hN : N≤160) (a : WeightedState) (t : ℝ) :
    vectorPolynomialEval (orderDisplacementPolynomial N a) t=orderTaylorPolynomial N a t-a := by
  rw [orderTaylorPolynomial_canonical N hN,add_sub_cancel_left]
  ext i
  simp only [vectorPolynomialEval,orderDisplacementPolynomial,eval_finsetSum,eval_monomial,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro n hn
  ring

lemma orderDisplacementPolynomial_derivative_eval {N : ℕ} (hN : N≤160)
    (a : WeightedState) (t : ℝ) :
    vectorPolynomialEval (vectorPolynomialDerivative (orderDisplacementPolynomial N a)) t=
      orderTaylorDerivative N a t := by
  ext i
  simp only [vectorPolynomialEval,vectorPolynomialDerivative,orderDisplacementPolynomial,
    derivative_sum,derivative_monomial,eval_finsetSum,eval_monomial,
    orderTaylorDerivative,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [fullTaylorCoeff_decompose a n (by have := Finset.mem_range.mp hn; omega)]
  by_cases hz : n=0
  · simp [hz]
  · simp only [hz,if_false,zero_add]
    ring

lemma orderDisplacementPolynomial_majorized {N : ℕ} (hN : N≤160)
    {a : WeightedState} (ha : a∈weightedTube) (n : ℕ) :
    ‖vectorPolynomialCoeff (orderDisplacementPolynomial N a) n‖≤
      (orderDisplacementMajorant N).coeff n := by
  rw [orderDisplacementPolynomial_coeff]
  split_ifs with hn
  · rw [orderDisplacementMajorant_agrees hN n (by omega)]
    exact canonicalTaylorCoeff_majorized ha n (by omega)
  · simpa only [norm_zero] using orderDisplacementMajorant_nonneg N n

def orderResidualPolynomial (N : ℕ) (a : WeightedState) : VectorPolynomial :=
  vectorPolynomialDerivative (orderDisplacementPolynomial N a)-
    polynomialField a (orderDisplacementPolynomial N a)

lemma orderResidualPolynomial_eval {N : ℕ} (hN : N≤160) (a : WeightedState) (t : ℝ) :
    vectorPolynomialEval (orderResidualPolynomial N a) t=
      orderTaylorDerivative N a t-weightedField (orderTaylorPolynomial N a t) := by
  rw [orderResidualPolynomial,vectorPolynomialEval_sub,
    orderDisplacementPolynomial_derivative_eval hN,polynomialField_eval,
    orderDisplacementPolynomial_eval hN,add_sub_cancel]

lemma orderResidualPolynomial_low (N : ℕ) (a : WeightedState) (n : ℕ) (hn : n<N) :
    vectorPolynomialCoeff (orderResidualPolynomial N a) n=0 := by
  rw [orderResidualPolynomial,vectorPolynomialCoeff_sub,vectorPolynomialDerivative_coeff,
    orderDisplacementPolynomial_coeff,if_pos (by omega),polynomialField_coeff]
  have he := vectorTaylorRHS_congr a (vectorPolynomialCoeff (orderDisplacementPolynomial N a))
    (canonicalTaylorCoeff a) n (by
      intro j hj
      rw [orderDisplacementPolynomial_coeff,if_pos (by omega)])
  rw [he,canonicalTaylorCoeff_recurrence,sub_self]

theorem orderResidualPolynomial_coeff_bound {N : ℕ} (hN : N≤160)
    {a : WeightedState} (ha : a∈weightedTube) (n : ℕ) :
    ‖vectorPolynomialCoeff (orderResidualPolynomial N a) n‖≤(orderScalarResidual N).coeff n := by
  by_cases hn : n<N
  · rw [orderResidualPolynomial_low N a n hn,norm_zero,orderScalarResidual_low hN n hn]
  · rw [orderResidualPolynomial,vectorPolynomialCoeff_sub,vectorPolynomialDerivative_coeff,
      orderDisplacementPolynomial_coeff,if_neg (by omega),smul_zero,zero_sub,norm_neg,
      polynomialField_coeff,← orderScalarForcing_high N n (by omega)]
    exact vectorTaylorRHS_bound_poly ha (orderDisplacementMajorant N)
      (orderDisplacementMajorant_nonneg N) _ n
      (fun j _=>orderDisplacementPolynomial_majorized hN ha j)

theorem orderTaylorPolynomial_residual_bound {N : ℕ} (hN : N≤160)
    {a : WeightedState} (ha : a∈weightedTube) {t : ℝ} (ht : 0≤t) :
    ‖orderTaylorDerivative N a t-weightedField (orderTaylorPolynomial N a t)‖≤
      (orderScalarResidual N).eval t := by
  rw [← orderResidualPolynomial_eval hN]
  exact vectorPolynomialEval_norm_bound (orderResidualPolynomial_coeff_bound hN ha) ht

/-- The actual order60 polynomial differential residual, with no analytic
series assumption and no residual hypothesis supplied by the caller. -/
theorem orderTaylor60_residual_uniform {a : WeightedState} (ha : a∈weightedTube)
    {t : ℝ} (ht : 0≤t) (htmax : t≤1/100) :
    ‖orderTaylorDerivative 60 a t-weightedField (orderTaylorPolynomial 60 a t)‖≤
      (finiteResidual60:ℝ) :=
  (orderTaylorPolynomial_residual_bound (by omega : 60≤160) ha ht).trans
    (orderScalarResidual60_uniform ht htmax)

end
end CentroidEscape.MetricStability

#print axioms CentroidEscape.MetricStability.orderTaylor60_residual_uniform

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape.MetricStability).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Variable-order actual residual audit passed for {checked} declarations."
