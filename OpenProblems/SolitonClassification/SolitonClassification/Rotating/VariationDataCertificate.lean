import SolitonClassification.Rotating.TaylorDataCertificate
import SolitonClassification.Rotating.VariationTaylor

/-! Fixed-mesh validation for each of all six variational columns. State and
matrix coefficients are checked separately against the same actual field. -/
namespace SolitonClassification.Rotating
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def fixedVariationRHS (S : ℕ) (c : ℕ → FixedVector) (q : ℕ → FixedBall)
    (w : ℕ → FixedVector) (n : ℕ) : FixedVector := fun i=>match i.val with
  | 0 => FixedBall.scale 8 (w n 1)
  | 1 => FixedBall.add
      (FixedBall.neg (FixedBall.divNat (FixedBall.scale 3 (fixedConvolution S q (fun j=>w j 0) n)) 16))
      (FixedBall.add (FixedBall.neg (FixedBall.divNat (w n 2) 8))
        (FixedBall.add
          (FixedBall.neg (FixedBall.divNat (fixedConvolution S (fun j=>c j 4) (fun j=>w j 3) n) 8))
          (FixedBall.neg (FixedBall.divNat (fixedConvolution S (fun j=>c j 3) (fun j=>w j 4) n) 8))))
  | 2 => FixedBall.add
      (FixedBall.neg (fixedConvolution S (fun j=>c j 0) (fun j=>w j 3) n))
      (FixedBall.neg (fixedConvolution S (fun j=>c j 3) (fun j=>w j 0) n))
  | 3 => FixedBall.add (fixedConvolution S (fun j=>c j 0) (fun j=>w j 2) n)
      (fixedConvolution S (fun j=>c j 2) (fun j=>w j 0) n)
  | 4 => FixedBall.zero
  | _ => w n 0

theorem fixedVariationRHS_contains {S : ℕ} (hS : 0<S)
    (c : ℕ → FixedVector) (q : ℕ → FixedBall) (w : ℕ → FixedVector)
    (x : ℕ → State) (y : ℕ → ℝ) (z : ℕ → State) (n : ℕ)
    (hc : ∀j≤n,∀i,(c j i).Contains S (x j i))
    (hq : ∀j≤n,(q j).Contains S (y j))
    (hw : ∀j≤n,∀i,(w j i).Contains S (z j i)) (i : Fin 6) :
    (fixedVariationRHS S c q w n i).Contains S (variationRHS x y z n i) := by
  have hconv (i k : Fin 6) := fixedConvolution_contains hS
    (fun j=>c j i) (fun j=>w j k) (fun j=>x j i) (fun j=>z j k) n
    (fun j hj=>hc j hj i) (fun j hj=>hw j hj k)
  have hsq := fixedConvolution_contains hS q (fun j=>w j 0) y (fun j=>z j 0) n
    hq (fun j hj=>hw j hj 0)
  fin_cases i
  · simpa [fixedVariationRHS,variationRHS] using FixedBall.contains_scale 8 (hw n le_rfl 1)
  · have h:=FixedBall.contains_add
      (FixedBall.contains_neg (FixedBall.contains_divNat hS (FixedBall.contains_scale 3 hsq) 16))
      (FixedBall.contains_add (FixedBall.contains_neg (FixedBall.contains_divNat hS (hw n le_rfl 2) 8))
        (FixedBall.contains_add (FixedBall.contains_neg (FixedBall.contains_divNat hS (hconv 4 3) 8))
          (FixedBall.contains_neg (FixedBall.contains_divNat hS (hconv 3 4) 8))))
    simpa [fixedVariationRHS,variationRHS,realConvolution,sub_eq_add_neg,add_assoc,neg_div,neg_mul] using h
  · simpa [fixedVariationRHS,variationRHS,realConvolution,sub_eq_add_neg] using
      FixedBall.contains_add (FixedBall.contains_neg (hconv 0 3)) (FixedBall.contains_neg (hconv 3 0))
  · simpa [fixedVariationRHS,variationRHS,realConvolution] using FixedBall.contains_add (hconv 0 2) (hconv 2 0)
  · simpa [fixedVariationRHS,variationRHS] using FixedBall.contains_zero S
  · exact hw n le_rfl 0

def fixedVariationNext (S n : ℕ) (st wt : FixedTaylorState) : Vector FixedBall 6 :=
  Vector.ofFn (fun i=>FixedBall.divNat
    (fixedVariationRHS S st.coefficient st.square wt.coefficient n i) (n+1))

def VariationDataValid (S N : ℕ) (st wt : FixedTaylorState) : Prop :=
  wt.coeffs.size=N+1 ∧ ∀n : Fin N,
    wt.coeffs[n.val+1]?.getD (Vector.ofFn zeroFixedVector)=fixedVariationNext S n st wt

instance (S N : ℕ) (st wt : FixedTaylorState) : Decidable (VariationDataValid S N st wt) :=
  inferInstanceAs (Decidable (_ ∧ ∀_ : Fin N,_))

theorem VariationDataValid.sound {S N : ℕ} {st wt : FixedTaylorState} {a v : State}
    (hS : 0<S) (hs : FixedTaylorInvariant S st a N)
    (hv : VariationDataValid S N st wt)
    (hw0 : ∀i,(wt.coefficient 0 i).Contains S (v i)) :
    ∀n≤N,∀i,(wt.coefficient n i).Contains S (variationCoeff a v n i) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn i
    cases n with
    | zero => simpa only [variationCoeff_zero] using hw0 i
    | succ n =>
      have hp : ∀j≤n,∀i,(wt.coefficient j i).Contains S (variationCoeff a v j i) := by
        intro j hj i; exact ih j (by omega) (by omega) i
      have h:=FixedBall.contains_divNat hS
        (fixedVariationRHS_contains hS st.coefficient st.square wt.coefficient
          (taylorCoeff a) (squareCoeff (taylorCoeff a)) (variationCoeff a v) n
          (fun j hj=>hs.coefficients j (by omega)) (fun j hj=>hs.squares j (by omega)) hp i) (n+1)
      have hr:=congrFun (variationCoeff_recurrence a v n) i
      have he : variationRHS (taylorCoeff a) (squareCoeff (taylorCoeff a)) (variationCoeff a v) n i/(n+1:ℝ)=
          variationCoeff a v (n+1) i := by
        simp only [Pi.smul_apply,smul_eq_mul] at hr
        rw [←hr]; field_simp
      have heq:=congrArg (fun w : Vector FixedBall 6=>w[i.val]) (hv.2 ⟨n,by omega⟩)
      change wt.coefficient (n+1) i=_ at heq
      rw [heq]
      simpa only [fixedVariationNext,Vector.getElem_ofFn,Nat.cast_add,Nat.cast_one,he] using h

theorem certifiedVariation_endpoint_contains {S N : ℕ} {st wt : FixedTaylorState} {a v : State}
    (hS : 0<S) (hs : FixedTaylorInvariant S st a N) (hv : VariationDataValid S N st wt)
    (hw0 : ∀i,(wt.coefficient 0 i).Contains S (v i)) (t : ℚ) (i : Fin 6) :
    (evaluateFixedTaylor S t wt N)[i.val].Contains S ((variationPolynomial a v N i).eval (t:ℝ)) := by
  have he : (variationPolynomial a v N i).eval (t:ℝ)=
      ∑j∈Finset.range (N+1),variationCoeff a v j i*(t:ℝ)^j := by
    simp [variationPolynomial,Polynomial.eval_finsetSum]
  rw [he]
  simpa only [evaluateFixedTaylor,Vector.getElem_ofFn,Nat.zero_add] using
    fixedHorner_contains hS (FixedBall.ofRat S t) (t:ℝ) (FixedBall.contains_ofRat hS t)
      (fun j=>wt.coefficient j i) (fun j=>variationCoeff a v j i) 0 (N+1)
      (fun j hj=>by simpa only [Nat.zero_add] using hv.sound hS hs hw0 j (by omega) i)

end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.certifiedVariation_endpoint_contains
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Full-six-column integer variational table audit passed."
