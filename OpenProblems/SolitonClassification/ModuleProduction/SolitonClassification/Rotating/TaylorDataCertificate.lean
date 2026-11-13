module

public import SolitonClassification.Rotating.FixedTaylor

@[expose] public section

/-! A small soundness bridge for materialized coefficient tables.
All entries are untrusted until their finite recurrence checks are proved.
This avoids recursively re-evaluating earlier coefficients inside the kernel. -/
namespace SolitonClassification.Rotating

def TaylorDataValid (S N : ℕ) (st : FixedTaylorState) : Prop :=
  st.coeffs.size=N+1 ∧ st.squares.size=N ∧
    ∀n : Fin N,
      st.square n=fixedTaylorNextSquare S n st ∧
      st.coeffs[n.val+1]?.getD (Vector.ofFn zeroFixedVector)=
        fixedTaylorNextCoeff S n st (st.square n)

instance (S N : ℕ) (st : FixedTaylorState) : Decidable (TaylorDataValid S N st) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀n : Fin N,_ ∧ _))

theorem TaylorDataValid.sound {S N : ℕ} {st : FixedTaylorState} {a : State}
    (hS : 0<S) (hv : TaylorDataValid S N st)
    (ha : ∀i,(st.coefficient 0 i).Contains S (a i)) :
    FixedTaylorInvariant S st a N := by
  have hc : ∀n≤N,∀i,(st.coefficient n i).Contains S (taylorCoeff a n i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn i
      cases n with
      | zero => simpa only [taylorCoeff_zero] using ha i
      | succ n =>
        have hp : ∀j≤n,∀i,(st.coefficient j i).Contains S (taylorCoeff a j i) := by
          intro j hj i; exact ih j (by omega) (by omega) i
        have hq : ∀j≤n,(st.square j).Contains S (squareCoeff (taylorCoeff a) j) := by
          intro j hj
          rw [(hv.2.2 ⟨j,by omega⟩).1]
          exact fixedConvolution_contains hS _ _ _ _ j
            (fun k hk => hp k (by omega) 0) (fun k hk => hp k (by omega) 0)
        have h := FixedBall.contains_divNat hS
          (fixedTaylorRHS_contains hS st.coefficient st.square
            (taylorCoeff a) (squareCoeff (taylorCoeff a)) n hp hq i) (n+1)
        have hr := congrFun (taylorCoeff_recurrence a n) i
        have he : realTaylorRHS (taylorCoeff a) (squareCoeff (taylorCoeff a)) n i/(n+1:ℝ)=
            taylorCoeff a (n+1) i := by
          simp only [Pi.smul_apply,smul_eq_mul] at hr
          rw [←hr]; field_simp
        have heq := congrArg (fun v : Vector FixedBall 6 => v[i.val])
          ((hv.2.2 ⟨n,by omega⟩).2)
        change st.coefficient (n+1) i=_ at heq
        rw [heq]
        have hqeq : (fun j => if j=n then st.square n else st.square j)=st.square := by
          funext j
          split_ifs with hj
          · rw [hj]
          · rfl
        simpa only [fixedTaylorNextCoeff,Vector.getElem_ofFn,hqeq,
          Nat.cast_add,Nat.cast_one,he] using h
  refine ⟨hv.1,hv.2.1,hc,?_⟩
  intro j hj
  rw [(hv.2.2 ⟨j,hj⟩).1]
  exact fixedConvolution_contains hS _ _ _ _ j
    (fun k hk=>hc k (by omega) 0) (fun k hk=>hc k (by omega) 0)

theorem certifiedTable_endpoint_contains {S N : ℕ} {st : FixedTaylorState} {a : State}
    (hS : 0<S) (hv : TaylorDataValid S N st)
    (ha : ∀i,(st.coefficient 0 i).Contains S (a i)) (t : ℚ) (i : Fin 6) :
    (evaluateFixedTaylor S t st N)[i.val].Contains S ((taylorPolynomial a N i).eval (t:ℝ)) :=
  evaluateFixedTaylor_contains hS t (hv.sound hS ha) i

end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.certifiedTable_endpoint_contains
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Materialized Taylor table soundness audit passed."

end
