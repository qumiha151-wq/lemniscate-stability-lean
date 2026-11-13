module

public import SolitonClassification.Rotating.TaylorDataCertificate
public import SolitonClassification.Rotating.PolynomialEnvelope

@[expose] public section

/-! Detailed finite state-residual certificates. The extended square and
high-degree residual entries are untrusted until exact recurrence checks
are supplied; their real polynomial meaning is then a theorem. -/
namespace SolitonClassification.Rotating
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open Polynomial

theorem FixedTaylorInvariant.polynomialCoefficient {S N : ℕ} {st : FixedTaylorState} {a : State}
    (hs : FixedTaylorInvariant S st a N) (n : ℕ) (i : Fin 6) :
    (st.coefficient n i).Contains S ((taylorPolynomial a N i).coeff n) := by
  by_cases hn : n≤N
  · rw [taylorPolynomial_coeff,if_pos hn]
    exact hs.coefficients n hn i
  · have hz : st.coeffs[n]?=none := Array.getElem?_eq_none (by rw [hs.coeff_size]; omega)
    simpa [taylorPolynomial_coeff,hn,FixedTaylorState.coefficient,hz,zeroFixedVector] using
      FixedBall.contains_zero S

def squareDataValue (q : Array FixedBall) (n : ℕ) : FixedBall := q[n]?.getD FixedBall.zero

def ExtendedSquareValid (S M : ℕ) (st : FixedTaylorState) (q : Array FixedBall) : Prop :=
  ∀n : Fin (M+1),squareDataValue q n=fixedTaylorNextSquare S n st

instance (S M : ℕ) (st : FixedTaylorState) (q : Array FixedBall) :
    Decidable (ExtendedSquareValid S M st q) := inferInstanceAs (Decidable (∀_ : Fin (M+1),_))

theorem ExtendedSquareValid.sound {S N M : ℕ} {st : FixedTaylorState} {a : State} {q : Array FixedBall}
    (hS : 0<S) (hs : FixedTaylorInvariant S st a N) (hq : ExtendedSquareValid S M st q)
    (n : ℕ) (hn : n≤M) : (squareDataValue q n).Contains S
      (squareCoeff (fun j i=>(taylorPolynomial a N i).coeff j) n) := by
  rw [hq ⟨n,by omega⟩]
  exact fixedConvolution_contains hS _ _ _ _ n
    (fun j _=>hs.polynomialCoefficient j 0) (fun j _=>hs.polynomialCoefficient j 0)

def fixedResidualNext (S n : ℕ) (st : FixedTaylorState) (q : Array FixedBall) : Vector FixedBall 6 :=
  Vector.ofFn (fun i=>FixedBall.neg (fixedTaylorRHS S st.coefficient (squareDataValue q) n i))

def residualDataValue (N : ℕ) (r : Array (Vector FixedBall 6)) (n : ℕ) : FixedVector := fun i=>
  if n<N then FixedBall.zero else (r[n-N]?.getD (Vector.ofFn zeroFixedVector))[i.val]

def StateResidualValid (S N M : ℕ) (st : FixedTaylorState) (q : Array FixedBall)
    (r : Array (Vector FixedBall 6)) : Prop :=
  ∀n : Fin (M+1),N≤n.val → r[n.val-N]?.getD (Vector.ofFn zeroFixedVector)=fixedResidualNext S n st q

instance (S N M : ℕ) (st : FixedTaylorState) (q : Array FixedBall) (r : Array (Vector FixedBall 6)) :
    Decidable (StateResidualValid S N M st q r) :=
  inferInstanceAs (Decidable (∀n : Fin (M+1),_→_))

theorem StateResidualValid.sound {S N M : ℕ} {st : FixedTaylorState} {a : State}
    {q : Array FixedBall} {r : Array (Vector FixedBall 6)}
    (hS : 0<S) (hs : FixedTaylorInvariant S st a N) (hq : ExtendedSquareValid S M st q)
    (hr : StateResidualValid S N M st q r) (n : ℕ) (hn : n≤M) (i : Fin 6) :
    (residualDataValue N r n i).Contains S ((taylorResidual a N i).coeff n) := by
  by_cases hlow : n<N
  · rw [taylorResidual_low_zero a N n hlow]
    simpa [residualDataValue,hlow] using FixedBall.contains_zero S
  · have heq:=hr (⟨n,by omega⟩ : Fin (M+1)) (by change N≤n; omega)
    simp only [residualDataValue,if_neg hlow,heq,fixedResidualNext,Vector.getElem_ofFn]
    have h:=FixedBall.contains_neg (fixedTaylorRHS_contains hS
      st.coefficient (squareDataValue q)
      (fun j i=>(taylorPolynomial a N i).coeff j)
      (squareCoeff (fun j i=>(taylorPolynomial a N i).coeff j)) n
      (fun j _=>hs.polynomialCoefficient j)
      (fun j hj=>hq.sound hS hs j (by omega)) i)
    have hp:=congrFun (polynomialField_coeff (taylorPolynomial a N) n) i
    have hd : (derivative (taylorPolynomial a N i)).coeff n=0 := by
      rw [coeff_derivative,taylorPolynomial_coeff,if_neg (by omega),zero_mul]
    simpa only [taylorResidual,coeff_sub,hd,hp,zero_sub] using h

theorem certifiedState_residual_bound {S N : ℕ} {st : FixedTaylorState} {a : State}
    {q : Array FixedBall} {r : Array (Vector FixedBall 6)} {h B : ℚ}
    (hS : 0<S) (hs : FixedTaylorInvariant S st a N)
    (hq : ExtendedSquareValid S (3*N) st q) (hr : StateResidualValid S N (3*N) st q r)
    (hB : 0≤B)
    (hb : ∀i,rationalEnvelope (fun n=>fixedAbsUpper S (residualDataValue N r n i)) h (3*N)≤B)
    {t : ℝ} (ht : |t|≤(h:ℝ)) : ‖polynomialPath (taylorResidual a N) t‖≤(B:ℝ) := by
  apply finitePolynomial_norm_bound (taylorResidual_degree a N) _ hB hb ht
  intro i n hn
  exact fixedAbsUpper_sound (hr.sound hS hs hq n hn i)

end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.certifiedState_residual_bound
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Finite integer state-residual certificate audit passed."

end
