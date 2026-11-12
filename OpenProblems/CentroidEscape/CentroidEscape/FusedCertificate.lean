import CentroidEscape.FusedTaylor

/-!
# Finite certificates at the requested order

Only N+1 coefficient vectors and N square coefficients are stored and checked.
For large concrete tables the stage equalities should be proved separately
and assembled into `FusedOrderTaylorDataValid`; the soundness theorem does not
require reducing one enormous Boolean check in a single kernel computation.
-/

namespace CentroidEscape
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- The certificate stores and verifies only the requested N Taylor stages. -/
def FusedOrderTaylorDataValid (S N : ℕ) (st : FixedTaylorState) : Prop :=
  st.coeffs.size=N+1 ∧ st.squares.size=N ∧ ∀ n : Fin N,
    st.square n.val=fusedTaylorNextSquare S n.val st ∧
    st.coeffs[n.val+1]?.getD (Vector.ofFn zeroFixedVector)=
      fusedTaylorNextCoeff S n.val st (st.square n.val)

instance (S N : ℕ) (st : FixedTaylorState) : Decidable (FusedOrderTaylorDataValid S N st) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀ _n : Fin N, _ ∧ _))

def checkFusedOrderTaylorData (S N : ℕ) (st : FixedTaylorState) : Bool := decide (FusedOrderTaylorDataValid S N st)

theorem fusedOrderTaylorData_sound {S : ℕ} (hS : 0<S) {N : ℕ} (hN : N≤160) {st : FixedTaylorState}
    (hcheck : checkFusedOrderTaylorData S N st=true) {a : WeightedState}
    (ha : ∀ i, (st.coefficient 0 i).Contains S (a i)) :
    FixedTaylorInvariant S st a N := by
  have hv : FusedOrderTaylorDataValid S N st := of_decide_eq_true hcheck
  have hc : ∀ n≤N, ∀ i, (st.coefficient n i).Contains S (fullTaylorCoeff a n i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn i
      cases n with
      | zero => simpa only [fullTaylorCoeff_zero] using ha i
      | succ n =>
        have hp : ∀ j≤n, ∀ k, (st.coefficient j k).Contains S (fullTaylorCoeff a j k) := by
          intro j hj k
          exact ih j (by omega) (by omega) k
        have hq : ∀ j≤n, (st.square j).Contains S (squareTaylorCoeff a j) := by
          intro j hj
          rw [(hv.2.2 ⟨j,by omega⟩).1, squareTaylorCoeff_eq]
          exact fusedConvolution_contains hS _ _ _ _ j
            (fun k hk => hp k (by omega) 4) (fun k hk => hp k (by omega) 4)
        have hh := FixedBall.contains_divNat hS
          (fusedTaylorRHS_contains hS st.coefficient
            (fun j => if j=n then st.square n else st.square j)
            (fullTaylorCoeff a) (squareTaylorCoeff a) n hp (by
              intro j hj
              by_cases he : j=n <;> simp only [he, if_true, if_false]
              · simpa only [he] using hq j hj
              · exact hq j hj) i) (n+1)
        have hr := congrFun (fullTaylorCoeff_recurrence a n (by omega)) i
        simp only [Pi.smul_apply, smul_eq_mul] at hr
        have hd : realTaylorRHS (fullTaylorCoeff a) (squareTaylorCoeff a) n i/(n+1:ℝ) =
            fullTaylorCoeff a (n+1) i := by
          rw [← hr]
          field_simp
        change ((st.coeffs[n+1]?.getD (Vector.ofFn zeroFixedVector))[i.val]).Contains S _
        rw [(hv.2.2 ⟨n,by omega⟩).2]
        simpa only [fusedTaylorNextCoeff, Vector.getElem_ofFn, Nat.cast_add,
          Nat.cast_one, hd] using hh
  constructor
  · exact hv.1
  · exact hv.2.1
  · exact hc
  · intro j hj
    rw [(hv.2.2 ⟨j,hj⟩).1, squareTaylorCoeff_eq]
    exact fusedConvolution_contains hS _ _ _ _ j
      (fun k hk => hc k (by omega) 4) (fun k hk => hc k (by omega) 4)

theorem checkedFusedOrderTaylorEndpoint_contains {S : ℕ} (hS : 0<S) {N : ℕ} (hN : N≤160) (t : ℚ)
    {st : FixedTaylorState} (hcheck : checkFusedOrderTaylorData S N st=true) {a : WeightedState}
    (ha : ∀ i, (st.coefficient 0 i).Contains S (a i)) (i : Fin 7) :
    (evaluateFixedTaylorOrder S N t st)[i.val].Contains S (orderTaylorPolynomial N a (t:ℝ) i) :=
  evaluateFixedTaylorOrder_contains hS N t (fusedOrderTaylorData_sound hS hN hcheck ha) i

end CentroidEscape

#print axioms CentroidEscape.checkedFusedOrderTaylorEndpoint_contains

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
  logInfo m!"Fused-certificate audit passed for {checked} declarations."


