import CentroidEscape.FixedTaylor

namespace CentroidEscape
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-!
# Finite integer Taylor certificates

A certificate supplies every coefficient and cached square as untrusted
integer data. The checker recomputes each single-step convolution against
those stored entries, rather than recursively recomputing earlier stages.
The soundness proof derives all real coefficient enclosures from these
finite arithmetic checks and an enclosed initial state.
-/

def FixedTaylorDataValid (S : ℕ) (st : FixedTaylorState) : Prop :=
  st.coeffs.size=161 ∧ st.squares.size=160 ∧ ∀ n : Fin 160,
    st.square n.val=fixedTaylorNextSquare S n.val st ∧
    st.coeffs[n.val+1]?.getD (Vector.ofFn zeroFixedVector)=
      fixedTaylorNextCoeff S n.val st (st.square n.val)

instance (S : ℕ) (st : FixedTaylorState) : Decidable (FixedTaylorDataValid S st) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀ _n : Fin 160, _ ∧ _))

def checkFixedTaylorData (S : ℕ) (st : FixedTaylorState) : Bool := decide (FixedTaylorDataValid S st)

theorem fixedTaylorData_sound {S : ℕ} (hS : 0<S) {st : FixedTaylorState}
    (hcheck : checkFixedTaylorData S st=true) {a : WeightedState}
    (ha : ∀ i, (st.coefficient 0 i).Contains S (a i)) :
    FixedTaylorInvariant S st a 160 := by
  have hv : FixedTaylorDataValid S st := of_decide_eq_true hcheck
  have hc : ∀ n≤160, ∀ i, (st.coefficient n i).Contains S (fullTaylorCoeff a n i) := by
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
          exact fixedConvolution_contains hS _ _ _ _ j
            (fun k hk => hp k (by omega) 4) (fun k hk => hp k (by omega) 4)
        have hh := FixedBall.contains_divNat hS
          (fixedTaylorRHS_contains hS st.coefficient
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
        simpa only [fixedTaylorNextCoeff, Vector.getElem_ofFn, Nat.cast_add,
          Nat.cast_one, hd] using hh
  constructor
  · exact hv.1
  · exact hv.2.1
  · exact hc
  · intro j hj
    rw [(hv.2.2 ⟨j,hj⟩).1, squareTaylorCoeff_eq]
    exact fixedConvolution_contains hS _ _ _ _ j
      (fun k hk => hc k (by omega) 4) (fun k hk => hc k (by omega) 4)

theorem checkedFixedTaylorEndpoint_contains {S : ℕ} (hS : 0<S) (t : ℚ)
    {st : FixedTaylorState} (hcheck : checkFixedTaylorData S st=true) {a : WeightedState}
    (ha : ∀ i, (st.coefficient 0 i).Contains S (a i)) (i : Fin 7) :
    (evaluateFixedTaylor S t st)[i.val].Contains S (canonicalTaylorPolynomial a (t:ℝ) i) :=
  evaluateFixedTaylor_contains hS t (fixedTaylorData_sound hS hcheck ha) i

end CentroidEscape

#print axioms CentroidEscape.checkedFixedTaylorEndpoint_contains

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
  logInfo m!"Fixed-certificate audit passed for {checked} declarations."
