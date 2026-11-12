import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms

/-!
# Computable rational balls with proved real containment

All arithmetic here is exact rational arithmetic. Quantization is directed
outwards and its rounding error is proved. Evaluating a certificate still
requires computing and checking its concrete finite operation sequence.
-/
namespace SolitonClassification.Rotating

structure RationalBall where
  center : ℚ
  radius : ℚ
  deriving DecidableEq

namespace RationalBall

def Contains (b : RationalBall) (x : ℝ) : Prop := |x-(b.center:ℝ)| ≤ (b.radius:ℝ)
def point (q : ℚ) : RationalBall := ⟨q,0⟩
def add (a b : RationalBall) : RationalBall := ⟨a.center+b.center,a.radius+b.radius⟩
def neg (a : RationalBall) : RationalBall := ⟨-a.center,a.radius⟩
def mul (a b : RationalBall) : RationalBall :=
  ⟨a.center*b.center, |a.center| * b.radius+|b.center| * a.radius+a.radius*b.radius⟩
def divNat (a : RationalBall) (n : ℕ) : RationalBall := ⟨a.center/n,a.radius/n⟩

theorem contains_point (q : ℚ) : (point q).Contains (q:ℝ) := by
  simp [Contains, point]

theorem radius_nonneg {b : RationalBall} {x : ℝ} (hx : b.Contains x) : 0 ≤ b.radius := by
  have : (0:ℝ) ≤ (b.radius:ℝ) := (abs_nonneg _).trans hx
  exact_mod_cast this

theorem contains_add {a b : RationalBall} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (add a b).Contains (x+y) := by
  unfold Contains add at *
  push_cast
  calc
    |x+y-((a.center:ℝ)+b.center)| = |(x-a.center)+(y-b.center)| := by congr 1; ring
    _ ≤ |x-a.center|+|y-b.center| := abs_add_le _ _
    _ ≤ _ := add_le_add hx hy

theorem contains_neg {a : RationalBall} {x : ℝ} (hx : a.Contains x) :
    (neg a).Contains (-x) := by
  change |-x-((-a.center:ℚ):ℝ)| ≤ (a.radius:ℝ)
  rw [Rat.cast_neg, sub_neg_eq_add, show -x+(a.center:ℝ) = -(x-(a.center:ℝ)) by ring, abs_neg]
  exact hx

theorem contains_mul {a b : RationalBall} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (mul a b).Contains (x*y) := by
  have hr : (0:ℝ) ≤ (a.radius:ℝ) := by exact_mod_cast radius_nonneg hx
  have hs : (0:ℝ) ≤ (b.radius:ℝ) := by exact_mod_cast radius_nonneg hy
  unfold Contains at hx hy ⊢
  simp only [mul, Rat.cast_add, Rat.cast_mul, Rat.cast_abs]
  calc
    |x*y-(a.center:ℝ)*b.center| =
      |(a.center:ℝ)*(y-b.center)+(b.center:ℝ)*(x-a.center)+(x-a.center)*(y-b.center)| := by
        congr 1; ring
    _ ≤ |(a.center:ℝ)*(y-b.center)|+|(b.center:ℝ)*(x-a.center)|+
        |(x-a.center)*(y-b.center)| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |(a.center:ℝ)| * |y-b.center|+|(b.center:ℝ)| * |x-a.center|+
        |x-a.center| * |y-b.center| := by simp only [abs_mul]
    _ ≤ _ := by gcongr

theorem contains_divNat {a : RationalBall} {x : ℝ} (hx : a.Contains x)
    (n : ℕ) : (divNat a n).Contains (x/n) := by
  unfold Contains divNat at *
  push_cast
  rw [← sub_div, abs_div]
  have hn : |(n:ℝ)| = (n:ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
  rw [hn]
  exact div_le_div_of_nonneg_right hx (Nat.cast_nonneg n)

def roundedCenter (S : ℕ) (q : ℚ) : ℚ := (⌊(S:ℚ)*q⌋:ℚ)/S
def round (S : ℕ) (a : RationalBall) : RationalBall :=
  ⟨roundedCenter S a.center, (⌈(S:ℚ)*(a.radius+1/S)⌉:ℚ)/S⟩

lemma roundedCenter_bounds {S : ℕ} (hS : 0 < S) (q : ℚ) :
    roundedCenter S q ≤ q ∧ q-roundedCenter S q ≤ 1/(S:ℚ) := by
  have hS' : (0:ℚ) < S := by exact_mod_cast hS
  have hlo := Int.floor_le ((S:ℚ)*q)
  have hhi := (Int.lt_floor_add_one ((S:ℚ)*q)).le
  unfold roundedCenter
  constructor
  · apply (div_le_iff₀ hS').2
    simpa [mul_comm] using hlo
  · apply (le_div_iff₀ hS').2
    field_simp
    have hhi' : q*(S:ℚ) ≤ (⌊q*(S:ℚ)⌋:ℚ)+1 := by simpa [mul_comm] using hhi
    linarith

theorem contains_round {a : RationalBall} {x : ℝ} {S : ℕ}
    (hS : 0 < S) (hx : a.Contains x) : (round S a).Contains x := by
  have hc := roundedCenter_bounds hS a.center
  have hc0 : (roundedCenter S a.center:ℝ) ≤ (a.center:ℝ) := by exact_mod_cast hc.1
  have hc1 : (a.center:ℝ)-(roundedCenter S a.center:ℝ) ≤ 1/(S:ℝ) := by
    have hcast : ((a.center-roundedCenter S a.center:ℚ):ℝ) ≤ ((1/(S:ℚ):ℚ):ℝ) := Rat.cast_le.mpr hc.2
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using hcast
  have hS' : (0:ℚ) < S := by exact_mod_cast hS
  have hrq : a.radius+1/(S:ℚ) ≤ (⌈(S:ℚ)*(a.radius+1/S)⌉:ℚ)/S := by
    apply (le_div_iff₀ hS').2
    simpa [mul_comm] using Int.le_ceil ((S:ℚ)*(a.radius+1/S))
  have hr : (a.radius:ℝ)+1/(S:ℝ) ≤ (((⌈(S:ℚ)*(a.radius+1/S)⌉:ℚ)/S):ℝ) := by
    have hcast : ((a.radius+1/(S:ℚ):ℚ):ℝ) ≤ (((⌈(S:ℚ)*(a.radius+1/S)⌉:ℚ)/(S:ℚ):ℚ):ℝ) := Rat.cast_le.mpr hrq
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using hcast
  unfold Contains round
  calc
    |x-(roundedCenter S a.center:ℝ)| =
      |(x-(a.center:ℝ))+((a.center:ℝ)-(roundedCenter S a.center:ℝ))| := by congr 1; ring
    _ ≤ |x-(a.center:ℝ)|+|(a.center:ℝ)-(roundedCenter S a.center:ℝ)| := abs_add_le _ _
    _ ≤ (a.radius:ℝ)+1/(S:ℝ) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hc0)]
      exact add_le_add hx hc1
    _ ≤ _ := by simpa only [Rat.cast_div, Rat.cast_natCast] using hr

def roundedAdd (S : ℕ) (a b : RationalBall) := round S (add a b)
def roundedMul (S : ℕ) (a b : RationalBall) := round S (mul a b)
def roundedDivNat (S : ℕ) (a : RationalBall) (n : ℕ) := round S (divNat a n)

theorem contains_roundedAdd {S : ℕ} (hS : 0 < S) {a b : RationalBall} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (roundedAdd S a b).Contains (x+y) :=
  contains_round hS (contains_add hx hy)

theorem contains_roundedMul {S : ℕ} (hS : 0 < S) {a b : RationalBall} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (roundedMul S a b).Contains (x*y) :=
  contains_round hS (contains_mul hx hy)

theorem contains_roundedDivNat {S : ℕ} (hS : 0 < S) {a : RationalBall} {x : ℝ}
    (hx : a.Contains x) (n : ℕ) : (roundedDivNat S a n).Contains (x/n) :=
  contains_round hS (contains_divNat hx n)

end RationalBall
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Rational-ball audit passed: {checked} declarations; standard axioms only."
