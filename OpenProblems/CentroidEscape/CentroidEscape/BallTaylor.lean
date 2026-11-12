import CentroidEscape.VectorPolynomial
import CentroidEscape.BallExpression

/-!
# Executable outward-rounded Taylor propagation

This module implements the actual weighted-field coefficient recurrence,
including its initial constant coefficient. The square of the curvature
series is cached, reducing the cubic calculation to quadratic total work in
the truncation order. Materialized coefficient vectors and arrays avoid
recursive reevaluation. All operations use rational balls with proved
directed rounding. The final endpoint enclosure is proved to contain the
canonical real Taylor polynomial, with no assumed coefficient enclosure.

The differential residual bound in `VectorPolynomial` supplies the separate
ODE truncation allowance. Concrete numerical execution and finite certificate
checking are separate from this algorithmic soundness theorem.
-/

namespace CentroidEscape
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

noncomputable def fullTaylorPolynomial (a : WeightedState) : VectorPolynomial :=
  constantVectorPolynomial a+canonicalDisplacementPolynomial a

noncomputable def fullTaylorCoeff (a : WeightedState) (n : ℕ) : WeightedState :=
  vectorPolynomialCoeff (fullTaylorPolynomial a) n

noncomputable def squareTaylorCoeff (a : WeightedState) (n : ℕ) : ℝ :=
  ((fullTaylorPolynomial a 4)^2).coeff n

noncomputable def directFieldPolynomial (P : VectorPolynomial) : VectorPolynomial :=
  ![C 4*P 2,C 4*P 3,C (-16)*(P 4*P 3),C 16*(P 4*P 2),C 4*P 5,
    C (-32)*((P 4)^2*P 4)+C (1/16)*(P 0*P 3-P 1*P 2),P 0]

lemma directFieldPolynomial_eq (a : WeightedState) (P : VectorPolynomial) :
    directFieldPolynomial (constantVectorPolynomial a+P) = polynomialField a P := by
  funext i
  fin_cases i <;> simp [directFieldPolynomial, constantVectorPolynomial, polynomialField,
    polynomialLinear, polynomialBilinear, polynomialTrilinear, weightedField, C_ofNat]
  all_goals dsimp [Matrix.vecHead, Matrix.vecTail, constantVectorPolynomial]
  all_goals simp only [div_eq_mul_inv, map_add, map_sub, map_mul, map_neg, map_pow, C_ofNat]
  all_goals ring

noncomputable def realTaylorRHS (c : ℕ → WeightedState) (q : ℕ → ℝ) (n : ℕ) : WeightedState :=
  ![4*c n 2,4*c n 3,
    -16*(∑ ij ∈ Finset.antidiagonal n, c ij.1 4*c ij.2 3),
    16*(∑ ij ∈ Finset.antidiagonal n, c ij.1 4*c ij.2 2),4*c n 5,
    -32*(∑ ij ∈ Finset.antidiagonal n, q ij.1*c ij.2 4)+
      ((∑ ij ∈ Finset.antidiagonal n, c ij.1 0*c ij.2 3)-
       (∑ ij ∈ Finset.antidiagonal n, c ij.1 1*c ij.2 2))/16,c n 0]

lemma directFieldPolynomial_coeff (P : VectorPolynomial) (n : ℕ) :
    vectorPolynomialCoeff (directFieldPolynomial P) n =
      realTaylorRHS (vectorPolynomialCoeff P) (fun j => ((P 4)^2).coeff j) n := by
  ext i
  fin_cases i <;> dsimp only [vectorPolynomialCoeff, directFieldPolynomial, realTaylorRHS]
  all_goals simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', coeff_add, coeff_C_mul,
    coeff_sub]
  all_goals try rw [coeff_mul]
  all_goals try simp only [coeff_mul]
  all_goals ring

lemma fullTaylorCoeff_zero (a : WeightedState) : fullTaylorCoeff a 0 = a := by
  simp [fullTaylorCoeff, fullTaylorPolynomial, vectorPolynomialCoeff_add,
    constantVectorPolynomial_coeff, canonicalDisplacementPolynomial_coeff, canonicalTaylorCoeff_zero]

lemma fullTaylorCoeff_pos (a : WeightedState) (n : ℕ) (hn : 0<n) (hN : n≤160) :
    fullTaylorCoeff a n = canonicalTaylorCoeff a n := by
  simp [fullTaylorCoeff, fullTaylorPolynomial, vectorPolynomialCoeff_add,
    constantVectorPolynomial_coeff, canonicalDisplacementPolynomial_coeff,
    show n≠0 by omega, show n<161 by omega]

lemma squareTaylorCoeff_eq (a : WeightedState) (n : ℕ) :
    squareTaylorCoeff a n =
      ∑ ij ∈ Finset.antidiagonal n, fullTaylorCoeff a ij.1 4*fullTaylorCoeff a ij.2 4 := by
  simp only [squareTaylorCoeff, pow_two, coeff_mul, fullTaylorCoeff, vectorPolynomialCoeff]

theorem fullTaylorCoeff_recurrence (a : WeightedState) (n : ℕ) (hn : n<160) :
    (n+1:ℝ) • fullTaylorCoeff a (n+1) =
      realTaylorRHS (fullTaylorCoeff a) (squareTaylorCoeff a) n := by
  have h := canonicalResidualPolynomial_coeff_low a n hn
  rw [canonicalResidualPolynomial, vectorPolynomialCoeff_sub,
    vectorPolynomialDerivative_coeff, canonicalDisplacementPolynomial_coeff,
    if_pos (by omega)] at h
  rw [fullTaylorCoeff_pos a (n+1) (by omega) (by omega)]
  change (n+1:ℝ) • canonicalTaylorCoeff a (n+1) =
    realTaylorRHS (vectorPolynomialCoeff (fullTaylorPolynomial a))
      (fun j => ((fullTaylorPolynomial a 4)^2).coeff j) n
  rw [← directFieldPolynomial_coeff]
  change (n+1:ℝ) • canonicalTaylorCoeff a (n+1) =
    vectorPolynomialCoeff (directFieldPolynomial (constantVectorPolynomial a+
      canonicalDisplacementPolynomial a)) n
  rw [directFieldPolynomial_eq]
  exact sub_eq_zero.mp h

abbrev BallVector := Fin 7 → RationalBall

def zeroBallVector : BallVector := fun _ => RationalBall.point 0

def ballListSum {α : Type} (S : ℕ) (f : α → RationalBall) : List α → RationalBall
  | [] => RationalBall.point 0
  | x::xs => RationalBall.roundedAdd S (f x) (ballListSum S f xs)

theorem ballListSum_contains {α : Type} {S : ℕ} (hS : 0<S)
    (l : List α) (b : α → RationalBall) (x : α → ℝ)
    (h : ∀ j ∈ l, (b j).Contains (x j)) :
    (ballListSum S b l).Contains (l.map x).sum := by
  induction l with
  | nil => simpa [ballListSum] using RationalBall.contains_point 0
  | cons j l ih =>
    simp only [ballListSum, List.map_cons, List.sum_cons]
    exact RationalBall.contains_roundedAdd hS (h j (by simp))
      (ih (fun k hk => h k (by simp [hk])))

def ballConvolution (S : ℕ) (b c : ℕ → RationalBall) (n : ℕ) : RationalBall :=
  ballListSum S (fun ij => RationalBall.roundedMul S (b ij.1) (c ij.2)) (List.Nat.antidiagonal n)

theorem ballConvolution_contains {S : ℕ} (hS : 0<S)
    (b c : ℕ → RationalBall) (x y : ℕ → ℝ) (n : ℕ)
    (hb : ∀ j≤n, (b j).Contains (x j)) (hc : ∀ j≤n, (c j).Contains (y j)) :
    (ballConvolution S b c n).Contains
      (∑ ij ∈ Finset.antidiagonal n, x ij.1*y ij.2) := by
  have hh := ballListSum_contains hS (List.Nat.antidiagonal n)
    (fun ij => RationalBall.roundedMul S (b ij.1) (c ij.2))
    (fun ij => x ij.1*y ij.2) (by
      intro ij hij
      have he := List.Nat.mem_antidiagonal.mp hij
      exact RationalBall.contains_roundedMul hS (hb ij.1 (by omega)) (hc ij.2 (by omega)))
  exact hh

def ballScale (S : ℕ) (q : ℚ) (b : RationalBall) :=
  RationalBall.roundedMul S (RationalBall.point q) b

theorem ballScale_contains {S : ℕ} (hS : 0<S) (q : ℚ)
    {b : RationalBall} {x : ℝ} (hb : b.Contains x) :
    (ballScale S q b).Contains ((q:ℝ)*x) :=
  RationalBall.contains_roundedMul hS (RationalBall.contains_point q) hb

def ballTaylorRHS (S : ℕ) (c : ℕ → BallVector) (q : ℕ → RationalBall) (n : ℕ) : BallVector :=
  fun i => match i.val with
  | 0 => ballScale S 4 (c n 2)
  | 1 => ballScale S 4 (c n 3)
  | 2 => ballScale S (-16) (ballConvolution S (fun j => c j 4) (fun j => c j 3) n)
  | 3 => ballScale S 16 (ballConvolution S (fun j => c j 4) (fun j => c j 2) n)
  | 4 => ballScale S 4 (c n 5)
  | 5 => RationalBall.roundedAdd S
      (ballScale S (-32) (ballConvolution S q (fun j => c j 4) n))
      (RationalBall.roundedDivNat S
        (RationalBall.roundedAdd S
          (ballConvolution S (fun j => c j 0) (fun j => c j 3) n)
          (RationalBall.neg (ballConvolution S (fun j => c j 1) (fun j => c j 2) n))) 16)
  | _ => c n 0

theorem ballTaylorRHS_contains {S : ℕ} (hS : 0<S)
    (c : ℕ → BallVector) (q : ℕ → RationalBall)
    (x : ℕ → WeightedState) (y : ℕ → ℝ) (n : ℕ)
    (hc : ∀ j≤n, ∀ i, (c j i).Contains (x j i))
    (hq : ∀ j≤n, (q j).Contains (y j)) (i : Fin 7) :
    (ballTaylorRHS S c q n i).Contains (realTaylorRHS x y n i) := by
  have hconv (i k : Fin 7) := ballConvolution_contains hS
    (fun j => c j i) (fun j => c j k) (fun j => x j i) (fun j => x j k) n
    (fun j hj => hc j hj i) (fun j hj => hc j hj k)
  have hsq := ballConvolution_contains hS q (fun j => c j 4) y (fun j => x j 4) n
    hq (fun j hj => hc j hj 4)
  fin_cases i
  · simpa [ballTaylorRHS, realTaylorRHS] using ballScale_contains hS 4 (hc n le_rfl 2)
  · simpa [ballTaylorRHS, realTaylorRHS] using ballScale_contains hS 4 (hc n le_rfl 3)
  · simpa [ballTaylorRHS, realTaylorRHS] using ballScale_contains hS (-16) (hconv 4 3)
  · simpa [ballTaylorRHS, realTaylorRHS] using ballScale_contains hS 16 (hconv 4 2)
  · simpa [ballTaylorRHS, realTaylorRHS] using ballScale_contains hS 4 (hc n le_rfl 5)
  · simpa [ballTaylorRHS, realTaylorRHS, sub_eq_add_neg] using
      RationalBall.contains_roundedAdd hS (ballScale_contains hS (-32) hsq)
        (RationalBall.contains_roundedDivNat hS
          (RationalBall.contains_roundedAdd hS (hconv 0 3)
            (RationalBall.contains_neg (hconv 1 2))) 16)
  · exact hc n le_rfl 0

/-- Coefficients are materialized vectors, so component arithmetic is cached,
not stored as unevaluated functions that re-run earlier convolutions. -/
structure BallTaylorState where
  coeffs : Array (Vector RationalBall 7)
  squares : Array RationalBall

def BallTaylorState.coefficient (st : BallTaylorState) (n : ℕ) : BallVector :=
  fun i => (st.coeffs[n]?.getD (Vector.ofFn zeroBallVector))[i.val]

def BallTaylorState.square (st : BallTaylorState) (n : ℕ) : RationalBall :=
  st.squares[n]?.getD (RationalBall.point 0)

def ballTaylorNextSquare (S n : ℕ) (st : BallTaylorState) : RationalBall :=
  ballConvolution S (fun j => st.coefficient j 4) (fun j => st.coefficient j 4) n

def ballTaylorNextCoeff (S n : ℕ) (st : BallTaylorState) (sq : RationalBall) :
    Vector RationalBall 7 :=
  Vector.ofFn (fun i => RationalBall.roundedDivNat S
    (ballTaylorRHS S st.coefficient (fun j => if j=n then sq else st.square j) n i) (n+1))

/-- Each step uses linear-sized convolution sums and pushes one cached square
and one materialized coefficient vector. The full order-N algorithm uses
O(N^2) rational operations. -/
def ballTaylorStep (S n : ℕ) (st : BallTaylorState) : BallTaylorState :=
  let sq := ballTaylorNextSquare S n st
  let c := ballTaylorNextCoeff S n st sq
  ⟨st.coeffs.push c,st.squares.push sq⟩

def initialBallTaylorState (b : BallVector) : BallTaylorState :=
  ⟨#[Vector.ofFn b],#[]⟩

def computeBallTaylor (S : ℕ) (b : BallVector) : ℕ → BallTaylorState
  | 0 => initialBallTaylorState b
  | n+1 => ballTaylorStep S n (computeBallTaylor S b n)

structure BallTaylorInvariant (st : BallTaylorState) (a : WeightedState) (n : ℕ) : Prop where
  coeff_size : st.coeffs.size=n+1
  square_size : st.squares.size=n
  coefficients : ∀ j≤n, ∀ i, (st.coefficient j i).Contains (fullTaylorCoeff a j i)
  squares : ∀ j<n, (st.square j).Contains (squareTaylorCoeff a j)

lemma initialBallTaylorState_sound {b : BallVector} {a : WeightedState}
    (ha : ∀ i, (b i).Contains (a i)) :
    BallTaylorInvariant (initialBallTaylorState b) a 0 := by
  constructor
  · rfl
  · rfl
  · intro j hj i
    have : j=0 := by omega
    subst j
    simpa [BallTaylorState.coefficient, initialBallTaylorState,
      fullTaylorCoeff_zero] using ha i
  · intro j hj
    omega

lemma ballTaylorStep_coefficient (S n : ℕ) (st : BallTaylorState) (j : ℕ) (i : Fin 7) :
    (ballTaylorStep S n st).coefficient j i =
      if j=st.coeffs.size then
        (ballTaylorNextCoeff S n st (ballTaylorNextSquare S n st))[i.val]
      else st.coefficient j i := by
  simp only [BallTaylorState.coefficient, ballTaylorStep, Array.getElem?_push]
  split_ifs <;> rfl

lemma ballTaylorStep_square (S n : ℕ) (st : BallTaylorState) (j : ℕ) :
    (ballTaylorStep S n st).square j =
      if j=st.squares.size then ballTaylorNextSquare S n st else st.square j := by
  simp only [BallTaylorState.square, ballTaylorStep, Array.getElem?_push]
  split_ifs <;> rfl

theorem ballTaylorStep_sound {S : ℕ} (hS : 0<S) {n : ℕ} (hn : n<160)
    {st : BallTaylorState} {a : WeightedState} (h : BallTaylorInvariant st a n) :
    BallTaylorInvariant (ballTaylorStep S n st) a (n+1) := by
  have hsq : (ballTaylorNextSquare S n st).Contains (squareTaylorCoeff a n) := by
    rw [squareTaylorCoeff_eq]
    exact ballConvolution_contains hS _ _ _ _ n
      (fun j hj => h.coefficients j hj 4) (fun j hj => h.coefficients j hj 4)
  have hqs : ∀ j≤n,
      (if j=n then ballTaylorNextSquare S n st else st.square j).Contains
        (squareTaylorCoeff a j) := by
    intro j hj
    by_cases he : j=n
    · subst j
      simpa using hsq
    · simpa [he] using h.squares j (by omega)
  have hc : ∀ i : Fin 7, ((ballTaylorNextCoeff S n st (ballTaylorNextSquare S n st))[i.val]).Contains
      (fullTaylorCoeff a (n+1) i) := by
    intro i
    have hh := RationalBall.contains_roundedDivNat hS
      (ballTaylorRHS_contains hS st.coefficient
        (fun j => if j=n then ballTaylorNextSquare S n st else st.square j)
        (fullTaylorCoeff a) (squareTaylorCoeff a) n h.coefficients hqs i) (n+1)
    have hr := congrFun (fullTaylorCoeff_recurrence a n hn) i
    simp only [Pi.smul_apply, smul_eq_mul] at hr
    have hd : realTaylorRHS (fullTaylorCoeff a) (squareTaylorCoeff a) n i/(n+1:ℝ) =
        fullTaylorCoeff a (n+1) i := by
      rw [← hr]
      field_simp
    simpa only [ballTaylorNextCoeff, Vector.getElem_ofFn, Nat.cast_add,
      Nat.cast_one, hd] using hh
  constructor
  · simpa only [ballTaylorStep, Array.size_push] using congrArg (·+1) h.coeff_size
  · simpa only [ballTaylorStep, Array.size_push] using congrArg (·+1) h.square_size
  · intro j hj i
    rw [ballTaylorStep_coefficient, h.coeff_size]
    by_cases he : j=n+1
    · subst j
      simpa using hc i
    · simpa [he] using h.coefficients j (by omega) i
  · intro j hj
    rw [ballTaylorStep_square, h.square_size]
    by_cases he : j=n
    · subst j
      simpa using hsq
    · simpa [he] using h.squares j (by omega)

/-- Executing the concrete array algorithm produces enclosures of the
canonical, actually constructed real Taylor coefficients through order 160. -/
theorem computeBallTaylor_sound {S : ℕ} (hS : 0<S) {b : BallVector} {a : WeightedState}
    (ha : ∀ i, (b i).Contains (a i)) (n : ℕ) (hn : n≤160) :
    BallTaylorInvariant (computeBallTaylor S b n) a n := by
  induction n with
  | zero => exact initialBallTaylorState_sound ha
  | succ n ih => exact ballTaylorStep_sound hS (by omega) (ih (by omega))

def ballHorner (S : ℕ) (t : ℚ) (b : ℕ → RationalBall) : ℕ → ℕ → RationalBall
  | _,0 => RationalBall.point 0
  | k,n+1 => RationalBall.roundedAdd S (b k)
      (RationalBall.roundedMul S (RationalBall.point t) (ballHorner S t b (k+1) n))

theorem ballHorner_contains {S : ℕ} (hS : 0<S) (t : ℚ)
    (b : ℕ → RationalBall) (x : ℕ → ℝ) (k n : ℕ)
    (hb : ∀ j<n, (b (k+j)).Contains (x (k+j))) :
    (ballHorner S t b k n).Contains
      (∑ j ∈ Finset.range n, x (k+j)*(t:ℝ)^j) := by
  induction n generalizing k with
  | zero => simpa [ballHorner] using RationalBall.contains_point 0
  | succ n ih =>
    have hh := RationalBall.contains_roundedAdd hS (hb 0 (by omega))
      (RationalBall.contains_roundedMul hS (RationalBall.contains_point t)
        (ih (k+1) (by
          intro j hj
          simpa only [add_assoc, Nat.add_comm 1 j] using hb (j+1) (by omega))))
    have he : x k+(t:ℝ)*(∑ j ∈ Finset.range n, x (k+1+j)*(t:ℝ)^j) =
        ∑ j ∈ Finset.range (n+1), x (k+j)*(t:ℝ)^j := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [Nat.add_zero, pow_zero, mul_one]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [show k+1+j=k+(j+1) by omega, pow_succ]
      ring
    simpa only [Nat.add_zero, he, ballHorner] using hh

lemma fullTaylorPolynomial_eval_sum (a : WeightedState) (t : ℝ) (i : Fin 7) :
    canonicalTaylorPolynomial a t i =
      ∑ j ∈ Finset.range 161, fullTaylorCoeff a j i*t^j := by
  have hdeg : (fullTaylorPolynomial a i).natDegree≤160 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    have hh : fullTaylorCoeff a j=0 := by
      simp [fullTaylorCoeff, fullTaylorPolynomial, vectorPolynomialCoeff_add,
        constantVectorPolynomial_coeff, canonicalDisplacementPolynomial_coeff,
        show j≠0 by omega, show ¬ j<161 by omega]
    exact congrFun hh i
  have he : vectorPolynomialEval (fullTaylorPolynomial a) t = canonicalTaylorPolynomial a t := by
    rw [fullTaylorPolynomial, vectorPolynomialEval_add, constantVectorPolynomial_eval,
      canonicalDisplacementPolynomial_eval, add_sub_cancel]
  rw [← congrFun he i]
  exact eval_eq_sum_range' (by omega : (fullTaylorPolynomial a i).natDegree<161) t

def evaluateBallTaylor (S : ℕ) (t : ℚ) (st : BallTaylorState) : Vector RationalBall 7 :=
  Vector.ofFn (fun i => ballHorner S t (fun j => st.coefficient j i) 0 161)

theorem evaluateBallTaylor_contains {S : ℕ} (hS : 0<S) (t : ℚ)
    {st : BallTaylorState} {a : WeightedState} (h : BallTaylorInvariant st a 160) (i : Fin 7) :
    (evaluateBallTaylor S t st)[i.val].Contains (canonicalTaylorPolynomial a (t:ℝ) i) := by
  rw [fullTaylorPolynomial_eval_sum]
  simpa only [evaluateBallTaylor, Vector.getElem_ofFn, Nat.zero_add] using
    ballHorner_contains hS t (fun j => st.coefficient j i) (fun j => fullTaylorCoeff a j i) 0 161
      (fun j hj => by simpa only [Nat.zero_add] using h.coefficients j (by omega) i)

/-- The output is a fully executable rational enclosure of the actual
canonical polynomial endpoint. The analytic ODE truncation allowance is
separate and provided by the proved vector residual theorem. -/
def ballTaylorEndpoint (S : ℕ) (t : ℚ) (b : BallVector) : Vector RationalBall 7 :=
  evaluateBallTaylor S t (computeBallTaylor S b 160)

theorem ballTaylorEndpoint_contains {S : ℕ} (hS : 0<S) (t : ℚ)
    {b : BallVector} {a : WeightedState} (ha : ∀ i, (b i).Contains (a i)) (i : Fin 7) :
    (ballTaylorEndpoint S t b)[i.val].Contains (canonicalTaylorPolynomial a (t:ℝ) i) :=
  evaluateBallTaylor_contains hS t (computeBallTaylor_sound hS ha 160 (by omega)) i

end CentroidEscape

#print axioms CentroidEscape.computeBallTaylor_sound
#print axioms CentroidEscape.ballTaylorEndpoint_contains

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
  logInfo m!"Ball-Taylor audit passed for {checked} declarations."
