module

public import SolitonClassification.Rotating.VariationDataCertificate

@[expose] public section

/-! State coefficients may be checked to order M and all variational columns
to a smaller order N. Soundness uses the already proved higher-order state
table directly, without truncating or rechecking it. This lemma does not
itself supply a tail bound or assert that a proposed order is sufficient. -/
namespace SolitonClassification.Rotating
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem VariationDataValid.sound_of_le {S N M : ℕ} {st wt : FixedTaylorState} {a v : State}
    (hS : 0<S) (hs : FixedTaylorInvariant S st a M) (hNM : N≤M)
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

theorem certifiedMixedVariation_endpoint_contains {S N M : ℕ} {st wt : FixedTaylorState} {a v : State}
    (hS : 0<S) (hs : FixedTaylorInvariant S st a M) (hNM : N≤M) (hv : VariationDataValid S N st wt)
    (hw0 : ∀i,(wt.coefficient 0 i).Contains S (v i)) (t : ℚ) (i : Fin 6) :
    (evaluateFixedTaylor S t wt N)[i.val].Contains S ((variationPolynomial a v N i).eval (t:ℝ)) := by
  have he : (variationPolynomial a v N i).eval (t:ℝ)=
      ∑j∈Finset.range (N+1),variationCoeff a v j i*(t:ℝ)^j := by
    simp [variationPolynomial,Polynomial.eval_finsetSum]
  rw [he]
  simpa only [evaluateFixedTaylor,Vector.getElem_ofFn,Nat.zero_add] using
    fixedHorner_contains hS (FixedBall.ofRat S t) (t:ℝ) (FixedBall.contains_ofRat hS t)
      (fun j=>wt.coefficient j i) (fun j=>variationCoeff a v j i) 0 (N+1)
      (fun j hj=>by simpa only [Nat.zero_add] using hv.sound_of_le hS hs hNM hw0 j (by omega) i)

end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.certifiedMixedVariation_endpoint_contains
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Mixed state/variation order soundness audit passed."

end
