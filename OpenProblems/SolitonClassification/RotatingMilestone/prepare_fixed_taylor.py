"""Adapt generic cached fixed-mesh machinery to this problem's real recurrence.

No compiled artifact or theorem from the centroid problem is imported.
The new six-component RHS below is derived from the rotating field.
"""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
src=ROOT.parent/'centroid_formal'/'FixedTaylor.lean'
old=src.read_text(encoding='utf-8').replace('\r','')
generic=old[old.index('def zeroFixedVector'):old.index('def fixedScale')]
body=old[old.index('/-- Coefficients are materialized vectors'):old.index('def evaluateFixedTaylor')]
for a,b in [('WeightedState','State'),('fullTaylorCoeff','taylorCoeff'),('squareTaylorCoeff','squareCoeff (taylorCoeff a)'),('Fin 7','Fin 6'),('FixedBall 7','FixedBall 6'),('coefficient j 4','coefficient j 0')]:
    body=body.replace(a,b)
body=body.replace('squareCoeff (taylorCoeff a) a','squareCoeff (taylorCoeff a)')
body=body.replace('rw [squareCoeff (taylorCoeff a)_eq]','change (fixedTaylorNextSquare S n st).Contains S (realConvolution (fun j => taylorCoeff a j 0) (fun j => taylorCoeff a j 0) n)')
body=body.replace('h.coefficients j hj 4','h.coefficients j hj 0')
body=body.replace('{n : ℕ} (hn : n<160)','{n : ℕ}')
body=body.replace('(taylorCoeff_recurrence a n hn)','(taylorCoeff_recurrence a n)')
body=body.replace('(n : ℕ) (hn : n≤160)','(n : ℕ)')
body=body.replace('exact fixedTaylorStep_sound hS (by omega) (ih (by omega))','exact fixedTaylorStep_sound hS ih')
body=body.replace('through order 160','through every finite order')
header='''import SolitonClassification.Rotating.FixedField
import SolitonClassification.Rotating.TaylorCoefficients

/-! Executable six-component coefficient recursion and Horner evaluation.
The output contains the canonical finite polynomial; an ODE tail is not
asserted here. Generic cache/induction machinery was independently copied
and specialized, with no import from another open problem. -/
namespace SolitonClassification.Rotating
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
abbrev FixedVector := Fin 6 → FixedBall

'''
rhs='''def fixedTaylorRHS (S : ℕ) (c : ℕ → FixedVector) (q : ℕ → FixedBall) (n : ℕ) : FixedVector :=
  fun i => match i.val with
  | 0 => FixedBall.scale 8 (c n 1)
  | 1 => FixedBall.add
      (FixedBall.neg (FixedBall.divNat (fixedConvolution S q (fun j => c j 0) n) 16))
      (FixedBall.add (FixedBall.neg (FixedBall.divNat (c n 2) 8))
        (FixedBall.neg (FixedBall.divNat
          (fixedConvolution S (fun j => c j 4) (fun j => c j 3) n) 8)))
  | 2 => FixedBall.neg (fixedConvolution S (fun j => c j 0) (fun j => c j 3) n)
  | 3 => FixedBall.add (if n=0 then FixedBall.ofRat S 1 else FixedBall.zero)
      (fixedConvolution S (fun j => c j 0) (fun j => c j 2) n)
  | 4 => FixedBall.zero
  | _ => c n 0

theorem fixedTaylorRHS_contains {S : ℕ} (hS : 0<S)
    (c : ℕ → FixedVector) (q : ℕ → FixedBall)
    (x : ℕ → State) (y : ℕ → ℝ) (n : ℕ)
    (hc : ∀ j≤n, ∀ i, (c j i).Contains S (x j i))
    (hq : ∀ j≤n, (q j).Contains S (y j)) (i : Fin 6) :
    (fixedTaylorRHS S c q n i).Contains S (realTaylorRHS x y n i) := by
  have hconv (i k : Fin 6) := fixedConvolution_contains hS
    (fun j => c j i) (fun j => c j k) (fun j => x j i) (fun j => x j k) n
    (fun j hj => hc j hj i) (fun j hj => hc j hj k)
  have hsq := fixedConvolution_contains hS q (fun j => c j 0) y (fun j => x j 0) n
    hq (fun j hj => hc j hj 0)
  fin_cases i
  · simpa [fixedTaylorRHS,realTaylorRHS] using FixedBall.contains_scale 8 (hc n le_rfl 1)
  · have h := FixedBall.contains_add
      (FixedBall.contains_neg (FixedBall.contains_divNat hS hsq 16))
      (FixedBall.contains_add (FixedBall.contains_neg (FixedBall.contains_divNat hS (hc n le_rfl 2) 8))
        (FixedBall.contains_neg (FixedBall.contains_divNat hS (hconv 4 3) 8)))
    simpa [fixedTaylorRHS,realTaylorRHS,realConvolution,sub_eq_add_neg,add_assoc,neg_div] using h
  · simpa [fixedTaylorRHS,realTaylorRHS,realConvolution] using FixedBall.contains_neg (hconv 0 3)
  · have hz : (if n=0 then FixedBall.ofRat S 1 else FixedBall.zero).Contains S
        (if n=0 then (1:ℝ) else 0) := by
      split_ifs
      · simpa using FixedBall.contains_ofRat hS 1
      · exact FixedBall.contains_zero S
    simpa [fixedTaylorRHS,realTaylorRHS,realConvolution] using FixedBall.contains_add hz (hconv 0 2)
  · simpa [fixedTaylorRHS,realTaylorRHS] using FixedBall.contains_zero S
  · exact hc n le_rfl 0

'''
footer='''def evaluateFixedTaylor (S : ℕ) (t : ℚ) (st : FixedTaylorState) (N : ℕ) : Vector FixedBall 6 :=
  let tb := FixedBall.ofRat S t
  Vector.ofFn (fun i => fixedHorner S tb (fun j => st.coefficient j i) 0 (N+1))

theorem evaluateFixedTaylor_contains {S : ℕ} (hS : 0<S) (t : ℚ)
    {st : FixedTaylorState} {a : State} {N : ℕ} (h : FixedTaylorInvariant S st a N) (i : Fin 6) :
    (evaluateFixedTaylor S t st N)[i.val].Contains S ((taylorPolynomial a N i).eval (t:ℝ)) := by
  have he : (taylorPolynomial a N i).eval (t:ℝ)=
      ∑ j ∈ Finset.range (N+1),taylorCoeff a j i*(t:ℝ)^j := by
    simp [taylorPolynomial,Polynomial.eval_finset_sum]
  rw [he]
  simpa only [evaluateFixedTaylor,Vector.getElem_ofFn,Nat.zero_add] using
    fixedHorner_contains hS (FixedBall.ofRat S t) (t:ℝ) (FixedBall.contains_ofRat hS t)
      (fun j => st.coefficient j i) (fun j => taylorCoeff a j i) 0 (N+1)
      (fun j hj => by simpa only [Nat.zero_add] using h.coefficients j (by omega) i)

def fixedTaylorEndpoint (S : ℕ) (t : ℚ) (b : FixedVector) (N : ℕ) : Vector FixedBall 6 :=
  evaluateFixedTaylor S t (computeFixedTaylor S b N) N

theorem fixedTaylorEndpoint_contains {S : ℕ} (hS : 0<S) (t : ℚ)
    {b : FixedVector} {a : State} (ha : ∀ i, (b i).Contains S (a i)) (N : ℕ) (i : Fin 6) :
    (fixedTaylorEndpoint S t b N)[i.val].Contains S ((taylorPolynomial a N i).eval (t:ℝ)) :=
  evaluateFixedTaylor_contains hS t (computeFixedTaylor_sound hS ha N) i

end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.computeFixedTaylor_sound
#print axioms SolitonClassification.Rotating.fixedTaylorEndpoint_contains

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
  logInfo "Rotating executable Taylor polynomial audit passed; standard axioms only."
'''
out=ROOT/'SolitonClassification'/'Rotating'/'FixedTaylor.lean'
out.write_text(header+generic+rhs+body+footer,encoding='utf-8')
(ROOT/'fixed_taylor_source_provenance.json').write_text(json.dumps({
    'source':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
    'scope':'Generic convolution, cache induction, and Horner proof adapted; new six-coordinate recurrence; no cross-problem imports.'},indent=2)+'\n')
