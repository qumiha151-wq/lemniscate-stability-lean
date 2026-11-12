import CentroidEscape.FixedTaylor

/-!
# Actual Taylor endpoints at a variable order

This module reuses the already proved coefficient-generation algorithm at
any requested N<=160. It evaluates only N+1 coefficients, proves the actual
finite curve's derivative and tube excursion, and proves integer-ball
endpoint containment. It does not assert an order-N ODE residual budget;
that requires the separately truncated scalar majorant and propagation bound.
-/

namespace CentroidEscape
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- The actual finite Taylor curve through order N. For N<=160 its positive
coefficients equal the previously constructed infinite canonical sequence. -/
def orderTaylorPolynomial (N : ℕ) (a : WeightedState) (t : ℝ) : WeightedState :=
  ∑ j ∈ Finset.range (N+1), t^j • fullTaylorCoeff a j

lemma fullTaylorCoeff_decompose (a : WeightedState) (j : ℕ) (hj : j≤160) :
    fullTaylorCoeff a j=(if j=0 then a else 0)+canonicalTaylorCoeff a j := by
  have hj' : j<161 := by omega
  simp only [fullTaylorCoeff, fullTaylorPolynomial, vectorPolynomialCoeff_add,
    constantVectorPolynomial_coeff, canonicalDisplacementPolynomial_coeff, if_pos hj']

lemma orderTaylorPolynomial_canonical (N : ℕ) (hN : N≤160) (a : WeightedState) (t : ℝ) :
    orderTaylorPolynomial N a t=a+∑ j ∈ Finset.range (N+1), t^j • canonicalTaylorCoeff a j := by
  unfold orderTaylorPolynomial
  calc
    _ = ∑ j ∈ Finset.range (N+1),
        (t^j • (if j=0 then a else 0)+t^j • canonicalTaylorCoeff a j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [fullTaylorCoeff_decompose a j (by have := Finset.mem_range.mp hj; omega), smul_add]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp [smul_ite]

lemma orderTaylorPolynomial_full (a : WeightedState) (t : ℝ) :
    orderTaylorPolynomial 160 a t=canonicalTaylorPolynomial a t := by
  rw [orderTaylorPolynomial_canonical 160 (by omega)]
  rfl

lemma orderTaylorPolynomial_zero (N : ℕ) (a : WeightedState) :
    orderTaylorPolynomial N a 0=a := by
  rw [orderTaylorPolynomial, Finset.sum_eq_single 0]
  · simp [fullTaylorCoeff_zero]
  · intro j hj hj0
    simp [zero_pow hj0]
  · simp

def orderTaylorDerivative (N : ℕ) (a : WeightedState) (t : ℝ) : WeightedState :=
  ∑ j ∈ Finset.range (N+1), ((j:ℝ)*t^(j-1)) • fullTaylorCoeff a j

theorem orderTaylorPolynomial_hasDerivAt (N : ℕ) (a : WeightedState) (t : ℝ) :
    HasDerivAt (orderTaylorPolynomial N a) (orderTaylorDerivative N a t) t := by
  apply HasDerivAt.fun_sum
  intro j hj
  simpa only [mul_one, Pi.pow_apply, id_eq] using
    ((hasDerivAt_id t).pow j).smul_const (fullTaylorCoeff a j)

theorem orderTaylorPolynomial_excursion {N : ℕ} (hN : N≤160) {a : WeightedState}
    (ha : a ∈ weightedTube) {t : ℝ} (ht : 0≤t) :
    ‖orderTaylorPolynomial N a t-a‖≤(majorantPoly t-1)/3 := by
  rw [orderTaylorPolynomial_canonical N hN, add_sub_cancel_left, ← displacementMajorant_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (N+1), t^j*displacementMajorant.coeff j := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht j)]
      exact mul_le_mul_of_nonneg_left
        (canonicalTaylorCoeff_majorized ha j (by have := Finset.mem_range.mp hj; omega))
        (pow_nonneg ht j)
    _ ≤ ∑ j ∈ Finset.range 161, t^j*displacementMajorant.coeff j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro j hj hnot
      exact mul_nonneg (pow_nonneg ht j) (displacementMajorant_nonneg j)

theorem orderTaylorPolynomial_excursion_uniform {N : ℕ} (hN : N≤160) {a : WeightedState}
    (ha : a ∈ weightedTube) {t : ℝ} (ht : 0≤t) (htmax : t≤1/100) :
    ‖orderTaylorPolynomial N a t-a‖<23/1000 :=
  lt_of_le_of_lt (orderTaylorPolynomial_excursion hN ha ht)
    (finite_majorant_excursion_uniform ht htmax).2

theorem orderTaylorPolynomial_in_tube {N : ℕ} (hN : N≤160) {a : WeightedState}
    (ha : ∀ i : Fin 7, i≠6 → |a i|≤tubeRadius i-23/1000)
    {t : ℝ} (ht : 0≤t) (htmax : t≤1/100) : orderTaylorPolynomial N a t ∈ weightedTube := by
  have hatube : a ∈ weightedTube := by intro i hi; linarith [ha i hi]
  have he := orderTaylorPolynomial_excursion_uniform hN hatube ht htmax
  intro i hi
  have hc : |orderTaylorPolynomial N a t i-a i|≤‖orderTaylorPolynomial N a t-a‖ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (orderTaylorPolynomial N a t-a) i
  have hh := abs_add_le (orderTaylorPolynomial N a t i-a i) (a i)
  rw [sub_add_cancel] at hh
  linarith [ha i hi]

end

/-- Only the requested N+1 coefficients are evaluated. -/
def evaluateFixedTaylorOrder (S N : ℕ) (t : ℚ) (st : FixedTaylorState) : Vector FixedBall 7 :=
  let tb := FixedBall.ofRat S t
  Vector.ofFn (fun i => fixedHorner S tb (fun j => st.coefficient j i) 0 (N+1))

theorem evaluateFixedTaylorOrder_contains {S : ℕ} (hS : 0<S) (N : ℕ) (t : ℚ)
    {st : FixedTaylorState} {a : WeightedState} (h : FixedTaylorInvariant S st a N) (i : Fin 7) :
    (evaluateFixedTaylorOrder S N t st)[i.val].Contains S (orderTaylorPolynomial N a (t:ℝ) i) := by
  have hh := fixedHorner_contains hS (FixedBall.ofRat S t) (t:ℝ) (FixedBall.contains_ofRat hS t)
    (fun j => st.coefficient j i) (fun j => fullTaylorCoeff a j i) 0 (N+1)
    (fun j hj => by simpa only [Nat.zero_add] using h.coefficients j (by omega) i)
  simpa only [evaluateFixedTaylorOrder, Vector.getElem_ofFn, Nat.zero_add, orderTaylorPolynomial,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hh

def fixedTaylorEndpointOrder (S N : ℕ) (t : ℚ) (b : FixedVector) : Vector FixedBall 7 :=
  evaluateFixedTaylorOrder S N t (computeFixedTaylor S b N)

theorem fixedTaylorEndpointOrder_contains {S : ℕ} (hS : 0<S) (N : ℕ) (hN : N≤160) (t : ℚ)
    {b : FixedVector} {a : WeightedState} (ha : ∀ i, (b i).Contains S (a i)) (i : Fin 7) :
    (fixedTaylorEndpointOrder S N t b)[i.val].Contains S (orderTaylorPolynomial N a (t:ℝ) i) :=
  evaluateFixedTaylorOrder_contains hS N t (computeFixedTaylor_sound hS ha N hN) i

end CentroidEscape

#print axioms CentroidEscape.fixedTaylorEndpointOrder_contains

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
  logInfo m!"Variable-order Taylor audit passed for {checked} declarations."
