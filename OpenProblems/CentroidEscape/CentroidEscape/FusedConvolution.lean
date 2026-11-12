import CentroidEscape.VariableOrderTaylor

/-!
# A single outward rounding for an entire convolution

Raw center and radius numerators are accumulated on mesh S^2 using only
integer multiplication and addition. The final sum is rounded to mesh S
once. This avoids two integer divisions per summand while preserving actual
real containment, proved through the existing rational-ball semantics.
-/

namespace CentroidEscape
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace FixedBall

/-- Exact product numerators on the squared mesh. No division is performed. -/
def rawProduct (a b : FixedBall) : FixedBall :=
  ⟨a.center*b.center, |a.center| * b.radius+|b.center| * a.radius+a.radius*b.radius⟩

/-- Round one accumulated squared-mesh ball back to the original mesh. -/
def rescaleSquared (S : ℕ) (a : FixedBall) : FixedBall :=
  ⟨a.center/(S:ℤ),ceilDiv a.radius S+1⟩

lemma rawProduct_toRational {S : ℕ} (hS : 0<S) (a b : FixedBall) :
    (rawProduct a b).toRational (S*S)=RationalBall.mul (a.toRational S) (b.toRational S) := by
  have hs : (S:ℚ)≠0 := by positivity
  have ha : |(S:ℚ)|=(S:ℚ) := abs_of_nonneg (Nat.cast_nonneg S)
  unfold rawProduct toRational RationalBall.mul
  congr 1
  · push_cast
    field_simp
  · simp only [Int.cast_add, Int.cast_mul, Int.cast_abs, Nat.cast_mul, abs_div, ha]
    field_simp

lemma rescaleSquared_toRational {S : ℕ} (hS : 0<S) (a : FixedBall) :
    (rescaleSquared S a).toRational S=RationalBall.round S (a.toRational (S*S)) := by
  have hs : (S:ℚ)≠0 := by positivity
  unfold rescaleSquared toRational RationalBall.round
  congr 1
  · unfold RationalBall.roundedCenter
    rw [show (S:ℚ)*((a.center:ℚ)/(S*S:ℕ))=(a.center:ℚ)/S by push_cast; field_simp,
      floor_div]
  · rw [show (S:ℚ)*((a.radius:ℚ)/(S*S:ℕ)+1/S)=(a.radius:ℚ)/S+1 by push_cast; field_simp,
      Int.ceil_add_one, ceil_div]

theorem rawProduct_contains {S : ℕ} (hS : 0<S) {a b : FixedBall} {x y : ℝ}
    (ha : a.Contains S x) (hb : b.Contains S y) : (rawProduct a b).Contains (S*S) (x*y) := by
  change ((rawProduct a b).toRational (S*S)).Contains (x*y)
  rw [rawProduct_toRational hS]
  exact RationalBall.contains_mul ha hb

theorem rescaleSquared_contains {S : ℕ} (hS : 0<S) {a : FixedBall} {x : ℝ}
    (ha : a.Contains (S*S) x) : (rescaleSquared S a).Contains S x := by
  change ((rescaleSquared S a).toRational S).Contains x
  rw [rescaleSquared_toRational hS]
  exact RationalBall.contains_round hS ha

end FixedBall

/-- Accumulate all exact integer product numerators, then round once. Unlike
fixedConvolution, this performs only two divisions for the entire sum. -/
def fusedConvolution (S : ℕ) (b c : ℕ → FixedBall) (n : ℕ) : FixedBall :=
  FixedBall.rescaleSquared S
    (fixedListSum (S*S) (fun ij => FixedBall.rawProduct (b ij.1) (c ij.2)) (List.Nat.antidiagonal n))

theorem fusedConvolution_contains {S : ℕ} (hS : 0<S)
    (b c : ℕ → FixedBall) (x y : ℕ → ℝ) (n : ℕ)
    (hb : ∀ j≤n, (b j).Contains S (x j)) (hc : ∀ j≤n, (c j).Contains S (y j)) :
    (fusedConvolution S b c n).Contains S
      (∑ ij ∈ Finset.antidiagonal n, x ij.1*y ij.2) := by
  apply FixedBall.rescaleSquared_contains hS
  have hh := fixedListSum_contains (Nat.mul_pos hS hS) (List.Nat.antidiagonal n)
    (fun ij => FixedBall.rawProduct (b ij.1) (c ij.2)) (fun ij => x ij.1*y ij.2) (by
      intro ij hij
      have he := List.Nat.mem_antidiagonal.mp hij
      exact FixedBall.rawProduct_contains hS (hb ij.1 (by omega)) (hc ij.2 (by omega)))
  exact hh

end CentroidEscape

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
  logInfo m!"Fused-convolution audit passed for {checked} declarations."
