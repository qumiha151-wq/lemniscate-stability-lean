import CentroidEscape.BallTaylor
import CentroidEscape.FixedBall

/-!
# Integer Taylor propagation with proved real meaning

The actual seven-coordinate Taylor algorithm caches the curvature square and
all prior coefficients in arrays. Every operation is fixed-mesh integer ball
arithmetic. The induction proves that its outputs contain the canonical real
coefficients already constructed in `VectorTaylor`. The Horner endpoint
theorem concludes containment of the actual canonical polynomial, without
assuming a numerical coefficient or endpoint certificate.
-/

namespace CentroidEscape
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
abbrev FixedVector := Fin 7 → FixedBall

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

def fixedScale (S : ℕ) (q : ℤ) (b : FixedBall) :=
  if 0<S then FixedBall.scale q b else FixedBall.zero

theorem fixedScale_contains {S : ℕ} (hS : 0<S) (q : ℤ)
    {b : FixedBall} {x : ℝ} (hb : b.Contains S x) :
    (fixedScale S q b).Contains S ((q:ℝ)*x) := by
  simpa only [fixedScale, if_pos hS] using FixedBall.contains_scale q hb
def fixedTaylorRHS (S : ℕ) (c : ℕ → FixedVector) (q : ℕ → FixedBall) (n : ℕ) : FixedVector :=
  fun i => match i.val with
  | 0 => fixedScale S 4 (c n 2)
  | 1 => fixedScale S 4 (c n 3)
  | 2 => fixedScale S (-16) (fixedConvolution S (fun j => c j 4) (fun j => c j 3) n)
  | 3 => fixedScale S 16 (fixedConvolution S (fun j => c j 4) (fun j => c j 2) n)
  | 4 => fixedScale S 4 (c n 5)
  | 5 => FixedBall.add
      (fixedScale S (-32) (fixedConvolution S q (fun j => c j 4) n))
      (FixedBall.divNat
        (FixedBall.add
          (fixedConvolution S (fun j => c j 0) (fun j => c j 3) n)
          (FixedBall.neg (fixedConvolution S (fun j => c j 1) (fun j => c j 2) n))) 16)
  | _ => c n 0

theorem fixedTaylorRHS_contains {S : ℕ} (hS : 0<S)
    (c : ℕ → FixedVector) (q : ℕ → FixedBall)
    (x : ℕ → WeightedState) (y : ℕ → ℝ) (n : ℕ)
    (hc : ∀ j≤n, ∀ i, (c j i).Contains S (x j i))
    (hq : ∀ j≤n, (q j).Contains S (y j)) (i : Fin 7) :
    (fixedTaylorRHS S c q n i).Contains S (realTaylorRHS x y n i) := by
  have hconv (i k : Fin 7) := fixedConvolution_contains hS
    (fun j => c j i) (fun j => c j k) (fun j => x j i) (fun j => x j k) n
    (fun j hj => hc j hj i) (fun j hj => hc j hj k)
  have hsq := fixedConvolution_contains hS q (fun j => c j 4) y (fun j => x j 4) n
    hq (fun j hj => hc j hj 4)
  fin_cases i
  · simpa [fixedTaylorRHS, realTaylorRHS] using fixedScale_contains hS 4 (hc n le_rfl 2)
  · simpa [fixedTaylorRHS, realTaylorRHS] using fixedScale_contains hS 4 (hc n le_rfl 3)
  · simpa [fixedTaylorRHS, realTaylorRHS] using fixedScale_contains hS (-16) (hconv 4 3)
  · simpa [fixedTaylorRHS, realTaylorRHS] using fixedScale_contains hS 16 (hconv 4 2)
  · simpa [fixedTaylorRHS, realTaylorRHS] using fixedScale_contains hS 4 (hc n le_rfl 5)
  · simpa [fixedTaylorRHS, realTaylorRHS, sub_eq_add_neg] using
      FixedBall.contains_add (fixedScale_contains hS (-32) hsq)
        (FixedBall.contains_divNat hS
          (FixedBall.contains_add (hconv 0 3)
            (FixedBall.contains_neg (hconv 1 2))) 16)
  · exact hc n le_rfl 0

/-- Coefficients are materialized vectors, so component arithmetic is cached,
not stored as unevaluated functions that re-run earlier convolutions. -/
structure FixedTaylorState where
  coeffs : Array (Vector FixedBall 7)
  squares : Array FixedBall

def FixedTaylorState.coefficient (st : FixedTaylorState) (n : ℕ) : FixedVector :=
  fun i => (st.coeffs[n]?.getD (Vector.ofFn zeroFixedVector))[i.val]

def FixedTaylorState.square (st : FixedTaylorState) (n : ℕ) : FixedBall :=
  st.squares[n]?.getD (FixedBall.zero)

def fixedTaylorNextSquare (S n : ℕ) (st : FixedTaylorState) : FixedBall :=
  fixedConvolution S (fun j => st.coefficient j 4) (fun j => st.coefficient j 4) n

def fixedTaylorNextCoeff (S n : ℕ) (st : FixedTaylorState) (sq : FixedBall) :
    Vector FixedBall 7 :=
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

structure FixedTaylorInvariant (S : ℕ) (st : FixedTaylorState) (a : WeightedState) (n : ℕ) : Prop where
  coeff_size : st.coeffs.size=n+1
  square_size : st.squares.size=n
  coefficients : ∀ j≤n, ∀ i, (st.coefficient j i).Contains S (fullTaylorCoeff a j i)
  squares : ∀ j<n, (st.square j).Contains S (squareTaylorCoeff a j)

lemma initialFixedTaylorState_sound {b : FixedVector} {a : WeightedState}
    (ha : ∀ i, (b i).Contains S (a i)) :
    FixedTaylorInvariant S (initialFixedTaylorState b) a 0 := by
  constructor
  · rfl
  · rfl
  · intro j hj i
    have : j=0 := by omega
    subst j
    simpa [FixedTaylorState.coefficient, initialFixedTaylorState,
      fullTaylorCoeff_zero] using ha i
  · intro j hj
    omega

lemma fixedTaylorStep_coefficient (S n : ℕ) (st : FixedTaylorState) (j : ℕ) (i : Fin 7) :
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

theorem fixedTaylorStep_sound {S : ℕ} (hS : 0<S) {n : ℕ} (hn : n<160)
    {st : FixedTaylorState} {a : WeightedState} (h : FixedTaylorInvariant S st a n) :
    FixedTaylorInvariant S (fixedTaylorStep S n st) a (n+1) := by
  have hsq : (fixedTaylorNextSquare S n st).Contains S (squareTaylorCoeff a n) := by
    rw [squareTaylorCoeff_eq]
    exact fixedConvolution_contains hS _ _ _ _ n
      (fun j hj => h.coefficients j hj 4) (fun j hj => h.coefficients j hj 4)
  have hqs : ∀ j≤n,
      (if j=n then fixedTaylorNextSquare S n st else st.square j).Contains S
        (squareTaylorCoeff a j) := by
    intro j hj
    by_cases he : j=n
    · subst j
      simpa using hsq
    · simpa [he] using h.squares j (by omega)
  have hc : ∀ i : Fin 7, ((fixedTaylorNextCoeff S n st (fixedTaylorNextSquare S n st))[i.val]).Contains S
      (fullTaylorCoeff a (n+1) i) := by
    intro i
    have hh := FixedBall.contains_divNat hS
      (fixedTaylorRHS_contains hS st.coefficient
        (fun j => if j=n then fixedTaylorNextSquare S n st else st.square j)
        (fullTaylorCoeff a) (squareTaylorCoeff a) n h.coefficients hqs i) (n+1)
    have hr := congrFun (fullTaylorCoeff_recurrence a n hn) i
    simp only [Pi.smul_apply, smul_eq_mul] at hr
    have hd : realTaylorRHS (fullTaylorCoeff a) (squareTaylorCoeff a) n i/(n+1:ℝ) =
        fullTaylorCoeff a (n+1) i := by
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
canonical, actually constructed real Taylor coefficients through order 160. -/
theorem computeFixedTaylor_sound {S : ℕ} (hS : 0<S) {b : FixedVector} {a : WeightedState}
    (ha : ∀ i, (b i).Contains S (a i)) (n : ℕ) (hn : n≤160) :
    FixedTaylorInvariant S (computeFixedTaylor S b n) a n := by
  induction n with
  | zero => exact initialFixedTaylorState_sound ha
  | succ n ih => exact fixedTaylorStep_sound hS (by omega) (ih (by omega))


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

def evaluateFixedTaylor (S : ℕ) (t : ℚ) (st : FixedTaylorState) : Vector FixedBall 7 :=
  let tb := FixedBall.ofRat S t
  Vector.ofFn (fun i => fixedHorner S tb (fun j => st.coefficient j i) 0 161)

theorem evaluateFixedTaylor_contains {S : ℕ} (hS : 0<S) (t : ℚ)
    {st : FixedTaylorState} {a : WeightedState} (h : FixedTaylorInvariant S st a 160) (i : Fin 7) :
    (evaluateFixedTaylor S t st)[i.val].Contains S (canonicalTaylorPolynomial a (t:ℝ) i) := by
  rw [fullTaylorPolynomial_eval_sum]
  simpa only [evaluateFixedTaylor, Vector.getElem_ofFn, Nat.zero_add] using
    fixedHorner_contains hS (FixedBall.ofRat S t) (t:ℝ) (FixedBall.contains_ofRat hS t)
      (fun j => st.coefficient j i) (fun j => fullTaylorCoeff a j i) 0 161
      (fun j hj => by simpa only [Nat.zero_add] using h.coefficients j (by omega) i)

def fixedTaylorEndpoint (S : ℕ) (t : ℚ) (b : FixedVector) : Vector FixedBall 7 :=
  evaluateFixedTaylor S t (computeFixedTaylor S b 160)

theorem fixedTaylorEndpoint_contains {S : ℕ} (hS : 0<S) (t : ℚ)
    {b : FixedVector} {a : WeightedState} (ha : ∀ i, (b i).Contains S (a i)) (i : Fin 7) :
    (fixedTaylorEndpoint S t b)[i.val].Contains S (canonicalTaylorPolynomial a (t:ℝ) i) :=
  evaluateFixedTaylor_contains hS t (computeFixedTaylor_sound hS ha 160 (by omega)) i

end CentroidEscape

#print axioms CentroidEscape.computeFixedTaylor_sound
#print axioms CentroidEscape.fixedTaylorEndpoint_contains

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
  logInfo m!"Fixed-Taylor audit passed for {checked} declarations."


