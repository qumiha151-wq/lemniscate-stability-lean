import CentroidEscape.FusedConvolution

/-!
# Actual Taylor propagation with fused integer convolutions

The canonical field recurrence is unchanged. Each of its quadratic
convolutions now accumulates exact integer numerators and rounds once.
The cached curvature square keeps the full order-N work quadratic. The
soundness theorem proves actual coefficient containment for N<=160 and
uses the variable-order Horner evaluator for the actual Taylor endpoint.
-/

namespace CentroidEscape
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def fusedTaylorRHS (S : ℕ) (c : ℕ → FixedVector) (q : ℕ → FixedBall) (n : ℕ) : FixedVector :=
  fun i => match i.val with
  | 0 => fixedScale S 4 (c n 2)
  | 1 => fixedScale S 4 (c n 3)
  | 2 => fixedScale S (-16) (fusedConvolution S (fun j => c j 4) (fun j => c j 3) n)
  | 3 => fixedScale S 16 (fusedConvolution S (fun j => c j 4) (fun j => c j 2) n)
  | 4 => fixedScale S 4 (c n 5)
  | 5 => FixedBall.add
      (fixedScale S (-32) (fusedConvolution S q (fun j => c j 4) n))
      (FixedBall.divNat
        (FixedBall.add
          (fusedConvolution S (fun j => c j 0) (fun j => c j 3) n)
          (FixedBall.neg (fusedConvolution S (fun j => c j 1) (fun j => c j 2) n))) 16)
  | _ => c n 0

theorem fusedTaylorRHS_contains {S : ℕ} (hS : 0<S)
    (c : ℕ → FixedVector) (q : ℕ → FixedBall)
    (x : ℕ → WeightedState) (y : ℕ → ℝ) (n : ℕ)
    (hc : ∀ j≤n, ∀ i, (c j i).Contains S (x j i))
    (hq : ∀ j≤n, (q j).Contains S (y j)) (i : Fin 7) :
    (fusedTaylorRHS S c q n i).Contains S (realTaylorRHS x y n i) := by
  have hconv (i k : Fin 7) := fusedConvolution_contains hS
    (fun j => c j i) (fun j => c j k) (fun j => x j i) (fun j => x j k) n
    (fun j hj => hc j hj i) (fun j hj => hc j hj k)
  have hsq := fusedConvolution_contains hS q (fun j => c j 4) y (fun j => x j 4) n
    hq (fun j hj => hc j hj 4)
  fin_cases i
  · simpa [fusedTaylorRHS, realTaylorRHS] using fixedScale_contains hS 4 (hc n le_rfl 2)
  · simpa [fusedTaylorRHS, realTaylorRHS] using fixedScale_contains hS 4 (hc n le_rfl 3)
  · simpa [fusedTaylorRHS, realTaylorRHS] using fixedScale_contains hS (-16) (hconv 4 3)
  · simpa [fusedTaylorRHS, realTaylorRHS] using fixedScale_contains hS 16 (hconv 4 2)
  · simpa [fusedTaylorRHS, realTaylorRHS] using fixedScale_contains hS 4 (hc n le_rfl 5)
  · simpa [fusedTaylorRHS, realTaylorRHS, sub_eq_add_neg] using
      FixedBall.contains_add (fixedScale_contains hS (-32) hsq)
        (FixedBall.contains_divNat hS
          (FixedBall.contains_add (hconv 0 3)
            (FixedBall.contains_neg (hconv 1 2))) 16)
  · exact hc n le_rfl 0

def fusedTaylorNextSquare (S n : ℕ) (st : FixedTaylorState) : FixedBall :=
  fusedConvolution S (fun j => st.coefficient j 4) (fun j => st.coefficient j 4) n

def fusedTaylorNextCoeff (S n : ℕ) (st : FixedTaylorState) (sq : FixedBall) :
    Vector FixedBall 7 :=
  Vector.ofFn (fun i => FixedBall.divNat
    (fusedTaylorRHS S st.coefficient (fun j => if j=n then sq else st.square j) n i) (n+1))

/-- Each step uses linear-sized convolution sums and pushes one cached square
and one materialized coefficient vector. The full order-N algorithm uses
O(N^2) rational operations. -/
def fusedTaylorStep (S n : ℕ) (st : FixedTaylorState) : FixedTaylorState :=
  let sq := fusedTaylorNextSquare S n st
  let c := fusedTaylorNextCoeff S n st sq
  ⟨st.coeffs.push c,st.squares.push sq⟩

def computeFusedTaylor (S : ℕ) (b : FixedVector) : ℕ → FixedTaylorState
  | 0 => initialFixedTaylorState b
  | n+1 => fusedTaylorStep S n (computeFusedTaylor S b n)

lemma fusedTaylorStep_coefficient (S n : ℕ) (st : FixedTaylorState) (j : ℕ) (i : Fin 7) :
    (fusedTaylorStep S n st).coefficient j i =
      if j=st.coeffs.size then
        (fusedTaylorNextCoeff S n st (fusedTaylorNextSquare S n st))[i.val]
      else st.coefficient j i := by
  simp only [FixedTaylorState.coefficient, fusedTaylorStep, Array.getElem?_push]
  split_ifs <;> rfl

lemma fusedTaylorStep_square (S n : ℕ) (st : FixedTaylorState) (j : ℕ) :
    (fusedTaylorStep S n st).square j =
      if j=st.squares.size then fusedTaylorNextSquare S n st else st.square j := by
  simp only [FixedTaylorState.square, fusedTaylorStep, Array.getElem?_push]
  split_ifs <;> rfl

theorem fusedTaylorStep_sound {S : ℕ} (hS : 0<S) {n : ℕ} (hn : n<160)
    {st : FixedTaylorState} {a : WeightedState} (h : FixedTaylorInvariant S st a n) :
    FixedTaylorInvariant S (fusedTaylorStep S n st) a (n+1) := by
  have hsq : (fusedTaylorNextSquare S n st).Contains S (squareTaylorCoeff a n) := by
    rw [squareTaylorCoeff_eq]
    exact fusedConvolution_contains hS _ _ _ _ n
      (fun j hj => h.coefficients j hj 4) (fun j hj => h.coefficients j hj 4)
  have hqs : ∀ j≤n,
      (if j=n then fusedTaylorNextSquare S n st else st.square j).Contains S
        (squareTaylorCoeff a j) := by
    intro j hj
    by_cases he : j=n
    · subst j
      simpa using hsq
    · simpa [he] using h.squares j (by omega)
  have hc : ∀ i : Fin 7, ((fusedTaylorNextCoeff S n st (fusedTaylorNextSquare S n st))[i.val]).Contains S
      (fullTaylorCoeff a (n+1) i) := by
    intro i
    have hh := FixedBall.contains_divNat hS
      (fusedTaylorRHS_contains hS st.coefficient
        (fun j => if j=n then fusedTaylorNextSquare S n st else st.square j)
        (fullTaylorCoeff a) (squareTaylorCoeff a) n h.coefficients hqs i) (n+1)
    have hr := congrFun (fullTaylorCoeff_recurrence a n hn) i
    simp only [Pi.smul_apply, smul_eq_mul] at hr
    have hd : realTaylorRHS (fullTaylorCoeff a) (squareTaylorCoeff a) n i/(n+1:ℝ) =
        fullTaylorCoeff a (n+1) i := by
      rw [← hr]
      field_simp
    simpa only [fusedTaylorNextCoeff, Vector.getElem_ofFn, Nat.cast_add,
      Nat.cast_one, hd] using hh
  constructor
  · simpa only [fusedTaylorStep, Array.size_push] using congrArg (·+1) h.coeff_size
  · simpa only [fusedTaylorStep, Array.size_push] using congrArg (·+1) h.square_size
  · intro j hj i
    rw [fusedTaylorStep_coefficient, h.coeff_size]
    by_cases he : j=n+1
    · subst j
      simpa using hc i
    · simpa [he] using h.coefficients j (by omega) i
  · intro j hj
    rw [fusedTaylorStep_square, h.square_size]
    by_cases he : j=n
    · subst j
      simpa using hsq
    · simpa [he] using h.squares j (by omega)

/-- Executing the concrete array algorithm produces enclosures of the
canonical, actually constructed real Taylor coefficients through order 160. -/
theorem computeFusedTaylor_sound {S : ℕ} (hS : 0<S) {b : FixedVector} {a : WeightedState}
    (ha : ∀ i, (b i).Contains S (a i)) (n : ℕ) (hn : n≤160) :
    FixedTaylorInvariant S (computeFusedTaylor S b n) a n := by
  induction n with
  | zero => exact initialFixedTaylorState_sound ha
  | succ n ih => exact fusedTaylorStep_sound hS (by omega) (ih (by omega))


def fusedTaylorEndpointOrder (S N : ℕ) (t : ℚ) (b : FixedVector) : Vector FixedBall 7 :=
  evaluateFixedTaylorOrder S N t (computeFusedTaylor S b N)

theorem fusedTaylorEndpointOrder_contains {S : ℕ} (hS : 0<S) (N : ℕ) (hN : N≤160) (t : ℚ)
    {b : FixedVector} {a : WeightedState} (ha : ∀ i, (b i).Contains S (a i)) (i : Fin 7) :
    (fusedTaylorEndpointOrder S N t b)[i.val].Contains S (orderTaylorPolynomial N a (t:ℝ) i) :=
  evaluateFixedTaylorOrder_contains hS N t (computeFusedTaylor_sound hS ha N hN) i

end CentroidEscape

#print axioms CentroidEscape.fusedTaylorEndpointOrder_contains

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
  logInfo m!"Fused-Taylor audit passed for {checked} declarations."
