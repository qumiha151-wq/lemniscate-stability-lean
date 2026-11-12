import SolitonClassification.Rotating.FixedField
import SolitonClassification.Rotating.TaylorCoefficients

/-! Executable six-component coefficient recursion and Horner evaluation.
The output contains the canonical finite polynomial; an ODE tail is not
asserted here. Generic cache/induction machinery was independently copied
and specialized, with no import from another open problem. -/
namespace SolitonClassification.Rotating
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
abbrev FixedVector := Fin 6 → FixedBall

def zeroFixedVector : FixedVector := fun _ => FixedBall.zero

def fixedListSum {α : Type} (S : ℕ) (f : α → FixedBall) : List α → FixedBall
  | [] => FixedBall.zero
  | x::xs => FixedBall.add (f x) (fixedListSum S f xs)

theorem fixedListSum_contains {α : Type} {S : ℕ} (_hS : 0<S)
    (l : List α) (b : α → FixedBall) (x : α → ℝ)
    (h : ∀ j ∈ l, (b j).Contains S (x j)) :
    (fixedListSum S b l).Contains S (l.map x).sum := by
  induction l with
  | nil => simpa [fixedListSum] using FixedBall.contains_zero S
  | cons j l ih =>
    simp only [fixedListSum, List.map_cons, List.sum_cons]
    exact FixedBall.contains_add (h j (by simp))
      (ih (fun k hk => h k (by simp [hk])))

def fixedConvolution (S : ℕ) (b c : ℕ → FixedBall) (n : ℕ) : FixedBall :=
  fixedListSum S (fun ij => FixedBall.mul S (b ij.1) (c ij.2)) (List.Nat.antidiagonal n)

theorem fixedConvolution_contains {S : ℕ} (hS : 0<S)
    (b c : ℕ → FixedBall) (x y : ℕ → ℝ) (n : ℕ)
    (hb : ∀ j≤n, (b j).Contains S (x j)) (hc : ∀ j≤n, (c j).Contains S (y j)) :
    (fixedConvolution S b c n).Contains S
      (∑ ij ∈ Finset.antidiagonal n, x ij.1*y ij.2) := by
  have hh := fixedListSum_contains hS (List.Nat.antidiagonal n)
    (fun ij => FixedBall.mul S (b ij.1) (c ij.2))
    (fun ij => x ij.1*y ij.2) (by
      intro ij hij
      have he := List.Nat.mem_antidiagonal.mp hij
      exact FixedBall.contains_mul hS (hb ij.1 (by omega)) (hc ij.2 (by omega)))
  exact hh

def fixedTaylorRHS (S : ℕ) (c : ℕ → FixedVector) (q : ℕ → FixedBall) (n : ℕ) : FixedVector :=
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

/-- Coefficients are materialized vectors, so component arithmetic is cached,
not stored as unevaluated functions that re-run earlier convolutions. -/
structure FixedTaylorState where
  coeffs : Array (Vector FixedBall 6)
  squares : Array FixedBall

def FixedTaylorState.coefficient (st : FixedTaylorState) (n : ℕ) : FixedVector :=
  fun i => (st.coeffs[n]?.getD (Vector.ofFn zeroFixedVector))[i.val]

def FixedTaylorState.square (st : FixedTaylorState) (n : ℕ) : FixedBall :=
  st.squares[n]?.getD (FixedBall.zero)

def fixedTaylorNextSquare (S n : ℕ) (st : FixedTaylorState) : FixedBall :=
  fixedConvolution S (fun j => st.coefficient j 0) (fun j => st.coefficient j 0) n

def fixedTaylorNextCoeff (S n : ℕ) (st : FixedTaylorState) (sq : FixedBall) :
    Vector FixedBall 6 :=
  Vector.ofFn (fun i => FixedBall.divNat
    (fixedTaylorRHS S st.coefficient (fun j => if j=n then sq else st.square j) n i) (n+1))

/-- Each step uses linear-sized convolution sums and pushes one cached square
and one materialized coefficient vector. The full order-N algorithm uses
O(N^2) rational operations. -/
def fixedTaylorStep (S n : ℕ) (st : FixedTaylorState) : FixedTaylorState :=
  let sq := fixedTaylorNextSquare S n st
  let c := fixedTaylorNextCoeff S n st sq
  ⟨st.coeffs.push c,st.squares.push sq⟩

def initialFixedTaylorState (b : FixedVector) : FixedTaylorState :=
  ⟨#[Vector.ofFn b],#[]⟩

def computeFixedTaylor (S : ℕ) (b : FixedVector) : ℕ → FixedTaylorState
  | 0 => initialFixedTaylorState b
  | n+1 => fixedTaylorStep S n (computeFixedTaylor S b n)

structure FixedTaylorInvariant (S : ℕ) (st : FixedTaylorState) (a : State) (n : ℕ) : Prop where
  coeff_size : st.coeffs.size=n+1
  square_size : st.squares.size=n
  coefficients : ∀ j≤n, ∀ i, (st.coefficient j i).Contains S (taylorCoeff a j i)
  squares : ∀ j<n, (st.square j).Contains S (squareCoeff (taylorCoeff a) j)

lemma initialFixedTaylorState_sound {b : FixedVector} {a : State}
    (ha : ∀ i, (b i).Contains S (a i)) :
    FixedTaylorInvariant S (initialFixedTaylorState b) a 0 := by
  constructor
  · rfl
  · rfl
  · intro j hj i
    have : j=0 := by omega
    subst j
    simpa [FixedTaylorState.coefficient, initialFixedTaylorState,
      taylorCoeff_zero] using ha i
  · intro j hj
    omega

lemma fixedTaylorStep_coefficient (S n : ℕ) (st : FixedTaylorState) (j : ℕ) (i : Fin 6) :
    (fixedTaylorStep S n st).coefficient j i =
      if j=st.coeffs.size then
        (fixedTaylorNextCoeff S n st (fixedTaylorNextSquare S n st))[i.val]
      else st.coefficient j i := by
  simp only [FixedTaylorState.coefficient, fixedTaylorStep, Array.getElem?_push]
  split_ifs <;> rfl

lemma fixedTaylorStep_square (S n : ℕ) (st : FixedTaylorState) (j : ℕ) :
    (fixedTaylorStep S n st).square j =
      if j=st.squares.size then fixedTaylorNextSquare S n st else st.square j := by
  simp only [FixedTaylorState.square, fixedTaylorStep, Array.getElem?_push]
  split_ifs <;> rfl

theorem fixedTaylorStep_sound {S : ℕ} (hS : 0<S) {n : ℕ}
    {st : FixedTaylorState} {a : State} (h : FixedTaylorInvariant S st a n) :
    FixedTaylorInvariant S (fixedTaylorStep S n st) a (n+1) := by
  have hsq : (fixedTaylorNextSquare S n st).Contains S (squareCoeff (taylorCoeff a) n) := by
    change (fixedTaylorNextSquare S n st).Contains S (realConvolution (fun j => taylorCoeff a j 0) (fun j => taylorCoeff a j 0) n)
    exact fixedConvolution_contains hS _ _ _ _ n
      (fun j hj => h.coefficients j hj 0) (fun j hj => h.coefficients j hj 0)
  have hqs : ∀ j≤n,
      (if j=n then fixedTaylorNextSquare S n st else st.square j).Contains S
        (squareCoeff (taylorCoeff a) j) := by
    intro j hj
    by_cases he : j=n
    · subst j
      simpa using hsq
    · simpa [he] using h.squares j (by omega)
  have hc : ∀ i : Fin 6, ((fixedTaylorNextCoeff S n st (fixedTaylorNextSquare S n st))[i.val]).Contains S
      (taylorCoeff a (n+1) i) := by
    intro i
    have hh := FixedBall.contains_divNat hS
      (fixedTaylorRHS_contains hS st.coefficient
        (fun j => if j=n then fixedTaylorNextSquare S n st else st.square j)
        (taylorCoeff a) (squareCoeff (taylorCoeff a)) n h.coefficients hqs i) (n+1)
    have hr := congrFun (taylorCoeff_recurrence a n) i
    simp only [Pi.smul_apply, smul_eq_mul] at hr
    have hd : realTaylorRHS (taylorCoeff a) (squareCoeff (taylorCoeff a)) n i/(n+1:ℝ) =
        taylorCoeff a (n+1) i := by
      rw [← hr]
      field_simp
    simpa only [fixedTaylorNextCoeff, Vector.getElem_ofFn, Nat.cast_add,
      Nat.cast_one, hd] using hh
  constructor
  · simpa only [fixedTaylorStep, Array.size_push] using congrArg (·+1) h.coeff_size
  · simpa only [fixedTaylorStep, Array.size_push] using congrArg (·+1) h.square_size
  · intro j hj i
    rw [fixedTaylorStep_coefficient, h.coeff_size]
    by_cases he : j=n+1
    · subst j
      simpa using hc i
    · simpa [he] using h.coefficients j (by omega) i
  · intro j hj
    rw [fixedTaylorStep_square, h.square_size]
    by_cases he : j=n
    · subst j
      simpa using hsq
    · simpa [he] using h.squares j (by omega)

/-- Executing the concrete array algorithm produces enclosures of the
canonical, actually constructed real Taylor coefficients through every finite order. -/
theorem computeFixedTaylor_sound {S : ℕ} (hS : 0<S) {b : FixedVector} {a : State}
    (ha : ∀ i, (b i).Contains S (a i)) (n : ℕ) :
    FixedTaylorInvariant S (computeFixedTaylor S b n) a n := by
  induction n with
  | zero => exact initialFixedTaylorState_sound ha
  | succ n ih => exact fixedTaylorStep_sound hS ih


def fixedHorner (S : ℕ) (t : FixedBall) (b : ℕ → FixedBall) : ℕ → ℕ → FixedBall
  | _,0 => FixedBall.zero
  | k,n+1 => FixedBall.add (b k) (FixedBall.mul S t (fixedHorner S t b (k+1) n))

theorem fixedHorner_contains {S : ℕ} (hS : 0<S) (t : FixedBall) (u : ℝ)
    (ht : t.Contains S u) (b : ℕ → FixedBall) (x : ℕ → ℝ) (k n : ℕ)
    (hb : ∀ j<n, (b (k+j)).Contains S (x (k+j))) :
    (fixedHorner S t b k n).Contains S
      (∑ j ∈ Finset.range n, x (k+j)*u^j) := by
  induction n generalizing k with
  | zero => simpa [fixedHorner] using FixedBall.contains_zero S
  | succ n ih =>
    have hh := FixedBall.contains_add (hb 0 (by omega))
      (FixedBall.contains_mul hS ht
        (ih (k+1) (by
          intro j hj
          simpa only [add_assoc, Nat.add_comm 1 j] using hb (j+1) (by omega))))
    have he : x k+u*(∑ j ∈ Finset.range n, x (k+1+j)*u^j) =
        ∑ j ∈ Finset.range (n+1), x (k+j)*u^j := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [Nat.add_zero, pow_zero, mul_one]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [show k+1+j=k+(j+1) by omega, pow_succ]
      ring
    simpa only [Nat.add_zero, he, fixedHorner] using hh

def evaluateFixedTaylor (S : ℕ) (t : ℚ) (st : FixedTaylorState) (N : ℕ) : Vector FixedBall 6 :=
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
