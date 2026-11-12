import CentroidEscape.BallStep

/-!
# A checked finite rational-ball grid encloses one genuine ODE trajectory

The executable state caches the endpoint vector and accumulated margin
check. A single globally existing clipped trajectory is propagated through
all cells; the local checked-step theorem proves that clipping is inactive
throughout. No local solutions are glued and no true-tube premise is used.
-/
namespace CentroidEscape
open Set
set_option backward.isDefEq.respectTransparency false

structure BallGridState where
  endpoint : Vector RationalBall 7
  checks : Bool

def BallGridState.ball (st : BallGridState) : BallVector := fun i => st.endpoint[i.val]

def initialBallGridState (b : BallVector) : BallGridState := ⟨Vector.ofFn b,true⟩

def advanceBallGrid (S : ℕ) (h : ℚ) (st : BallGridState) : BallGridState :=
  ⟨ballCanonicalStep S h st.ball, st.checks && checkBallCanonicalMargin st.ball⟩

/-- Each recursion evaluates the previous state once and reuses its
materialized endpoint. The Bool checks every input cell of the grid. -/
def computeBallGrid (S : ℕ) (h : ℚ) (b : BallVector) : ℕ → BallGridState
  | 0 => initialBallGridState b
  | n+1 => advanceBallGrid S h (computeBallGrid S h b n)

lemma computeBallGrid_checks {S N : ℕ} {h : ℚ} {b : BallVector}
    (hc : (computeBallGrid S h b N).checks = true) :
    ∀ n<N, checkBallCanonicalMargin (computeBallGrid S h b n).ball = true := by
  induction N with
  | zero => intro n hn; omega
  | succ N ih =>
    change ((computeBallGrid S h b N).checks &&
      checkBallCanonicalMargin (computeBallGrid S h b N).ball) = true at hc
    have hh : (computeBallGrid S h b N).checks = true ∧
        checkBallCanonicalMargin (computeBallGrid S h b N).ball = true := by
      simpa using hc
    intro n hn
    by_cases he : n=N
    · simpa only [he] using hh.2
    · exact ih hh.1 n (by omega)

lemma ball_grid_cell_time {h : ℝ} (hh : 0 ≤ h) {N j : ℕ} (hj : j<N)
    {r : ℝ} (hr : r ∈ Icc 0 h) : (j:ℝ)*h+r ∈ Icc 0 ((N:ℝ)*h) := by
  have hj' : (j:ℝ)+1 ≤ (N:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hj
  constructor
  · exact add_nonneg (mul_nonneg (Nat.cast_nonneg j) hh) hr.1
  · calc
      (j:ℝ)*h+r ≤ ((j:ℝ)+1)*h := by nlinarith [hr.2]
      _ ≤ (N:ℝ)*h := mul_le_mul_of_nonneg_right hj' hh

theorem clipped_trajectory_ball_grid_cell {S N j : ℕ} (hS : 0<S)
    {h : ℚ} (hh : 0 ≤ h) (hhmax : h ≤ 1/100) (hj : j<N)
    {b : BallVector} (hb : checkBallCanonicalMargin b = true)
    {z : ℝ → WeightedState}
    (hz : ∀ t ∈ Icc 0 ((N:ℝ)*(h:ℝ)), HasDerivAt z (clippedField (z t)) t)
    (hstart : ∀ i, (b i).Contains (z ((j:ℝ)*(h:ℝ)) i)) :
    (∀ r ∈ Icc 0 (h:ℝ), z ((j:ℝ)*(h:ℝ)+r) ∈ weightedTube) ∧
      (∀ r ∈ Icc 0 (h:ℝ), HasDerivAt z
        (weightedField (z ((j:ℝ)*(h:ℝ)+r))) ((j:ℝ)*(h:ℝ)+r)) ∧
      (∀ i : Fin 7, (ballCanonicalStep S h b)[i.val].Contains
        (z (((j+1:ℕ):ℝ)*(h:ℝ)) i)) := by
  have hh' : (0:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hw : ∀ r ∈ Icc 0 (h:ℝ), HasDerivAt
      (fun s => z ((j:ℝ)*(h:ℝ)+s))
      (clippedField (z ((j:ℝ)*(h:ℝ)+r))) r := by
    intro r hr
    have hs : HasDerivAt (fun s : ℝ => (j:ℝ)*(h:ℝ)+s) 1 r := by
      simpa using ((hasDerivAt_id r).const_add ((j:ℝ)*(h:ℝ)))
    convert! (hz _ (ball_grid_cell_time hh' hj hr)).scomp r hs using 1
    simp
  have hs := checked_clipped_trajectory_ballCanonicalStep hS hh hhmax hb
    (w := fun r => z ((j:ℝ)*(h:ℝ)+r))
    (by simpa only [add_zero] using hstart) hw
  refine ⟨hs.2.1, ?_, ?_⟩
  · intro r hr
    simpa only [clippedField_eq (hs.2.1 r hr)] using
      hz _ (ball_grid_cell_time hh' hj hr)
  · intro i
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hs.2.2 i

/-- All grid nodes and all intervening cells of any true clipped trajectory
are certified by successful finite rational margin checks. -/
theorem checked_ball_grid_trajectory {S N : ℕ} (hS : 0<S)
    {h : ℚ} (hh : 0 ≤ h) (hhmax : h ≤ 1/100) {b : BallVector}
    (hc : (computeBallGrid S h b N).checks = true)
    {z : ℝ → WeightedState} (hz0 : ∀ i, (b i).Contains (z 0 i))
    (hz : ∀ t ∈ Icc 0 ((N:ℝ)*(h:ℝ)), HasDerivAt z (clippedField (z t)) t) :
    (∀ n≤N, ∀ i, ((computeBallGrid S h b n).ball i).Contains
      (z ((n:ℝ)*(h:ℝ)) i)) ∧
    (∀ j<N, ∀ r ∈ Icc 0 (h:ℝ), z ((j:ℝ)*(h:ℝ)+r) ∈ weightedTube) ∧
    (∀ j<N, ∀ r ∈ Icc 0 (h:ℝ), HasDerivAt z
      (weightedField (z ((j:ℝ)*(h:ℝ)+r))) ((j:ℝ)*(h:ℝ)+r)) := by
  have hchecks := computeBallGrid_checks hc
  have hend : ∀ n≤N, ∀ i, ((computeBallGrid S h b n).ball i).Contains
      (z ((n:ℝ)*(h:ℝ)) i) := by
    intro n hn
    induction n with
    | zero =>
      simpa only [computeBallGrid, initialBallGridState, BallGridState.ball,
        Vector.getElem_ofFn, Nat.cast_zero, zero_mul] using hz0
    | succ n ih =>
      have hnN : n<N := by omega
      exact (clipped_trajectory_ball_grid_cell hS hh hhmax hnN (hchecks n hnN) hz
        (ih (by omega))).2.2
  refine ⟨hend, ?_, ?_⟩
  · intro j hj
    exact (clipped_trajectory_ball_grid_cell hS hh hhmax hj (hchecks j hj) hz
      (hend j (by omega))).1
  · intro j hj
    exact (clipped_trajectory_ball_grid_cell hS hh hhmax hj (hchecks j hj) hz
      (hend j (by omega))).2.1

lemma nonnegative_grid_covers {h : ℝ} (_hh : 0 ≤ h) (N : ℕ) (hN : 0<N)
    {t : ℝ} (ht : t ∈ Icc 0 ((N:ℝ)*h)) :
    ∃ j<N, ∃ r ∈ Icc 0 h, t=(j:ℝ)*h+r := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hn : N=0
    · subst N
      exact ⟨0,by omega,t,by simpa using ht,by simp⟩
    · by_cases hle : t ≤ (N:ℝ)*h
      · obtain ⟨j,hj,r,hr,he⟩ := ih (by omega) ⟨ht.1,hle⟩
        exact ⟨j,by omega,r,hr,he⟩
      · refine ⟨N,by omega,t-(N:ℝ)*h,?_,by ring⟩
        constructor
        · linarith
        · have htop := ht.2
          simp only [Nat.cast_add, Nat.cast_one] at htop
          nlinarith

/-- Successful exact-rational grid checks give an actual original-field
solution on the entire interval and enclose every grid endpoint. The true
trajectory's tube membership and inactivity of clipping are conclusions. -/
theorem exists_checked_ball_grid {S N : ℕ} (hS : 0<S) (hN : 0<N)
    {h : ℚ} (hh : 0 ≤ h) (hhmax : h ≤ 1/100) {b : BallVector}
    (hc : (computeBallGrid S h b N).checks = true) {a : WeightedState}
    (ha : ∀ i, (b i).Contains (a i)) :
    ∃ z : ℝ → WeightedState, z 0=a ∧
      (∀ t ∈ Icc 0 ((N:ℝ)*(h:ℝ)), HasDerivAt z (weightedField (z t)) t) ∧
      (∀ t ∈ Icc 0 ((N:ℝ)*(h:ℝ)), z t ∈ weightedTube) ∧
      (∀ n≤N, ∀ i, ((computeBallGrid S h b n).ball i).Contains
        (z ((n:ℝ)*(h:ℝ)) i)) := by
  have hh' : (0:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  obtain ⟨z,hz0,hz⟩ := exists_ode_on_finite_interval clippedField 8 2 a
    ((N:ℝ)*(h:ℝ)) (mul_nonneg (Nat.cast_nonneg N) hh')
    clippedField_lipschitz clippedField_bound
  have hs := checked_ball_grid_trajectory hS hh hhmax hc
    (by simpa only [hz0] using ha) hz
  refine ⟨z,hz0,?_,?_,hs.1⟩
  · intro t ht
    obtain ⟨j,hj,r,hr,he⟩ := nonnegative_grid_covers hh' N hN ht
    simpa only [he] using hs.2.2 j hj r hr
  · intro t ht
    obtain ⟨j,hj,r,hr,he⟩ := nonnegative_grid_covers hh' N hN ht
    simpa only [he] using hs.2.1 j hj r hr

end CentroidEscape

#print axioms CentroidEscape.exists_checked_ball_grid

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
  logInfo m!"Ball-grid audit passed for {checked} declarations."
