module

public import SolitonClassification.Rotating.RationalBall

@[expose] public section

/-!
# Fixed-mesh integer balls

Arithmetic uses integer numerators with one shared positive mesh denominator.
Products and division use integer floor/ceiling operations; their rational
semantics equal the existing proved outward-rounded operations. Addition and
integer scaling are exact on the shared mesh. Thus this backend avoids the
repeated rational normalization in the original evaluator while retaining
the same real containment meaning.
-/

namespace SolitonClassification.Rotating

/-- Shared-mesh integer ball: the represented interval is c/S ± r/S. -/
structure FixedBall where
  center : ℤ
  radius : ℤ
  deriving DecidableEq, Repr

namespace FixedBall

def toRational (S : ℕ) (b : FixedBall) : RationalBall :=
  ⟨(b.center:ℚ)/S,(b.radius:ℚ)/S⟩

def Contains (S : ℕ) (b : FixedBall) (x : ℝ) : Prop := (b.toRational S).Contains x

def zero : FixedBall := ⟨0,0⟩
def add (a b : FixedBall) : FixedBall := ⟨a.center+b.center,a.radius+b.radius⟩
def neg (a : FixedBall) : FixedBall := ⟨-a.center,a.radius⟩
def scale (k : ℤ) (a : FixedBall) : FixedBall := ⟨k*a.center,|k| *a.radius⟩
def ceilDiv (a : ℤ) (n : ℕ) : ℤ := -((-a)/(n:ℤ))
def mul (S : ℕ) (a b : FixedBall) : FixedBall :=
  ⟨a.center*b.center/(S:ℤ),
    ceilDiv (|a.center| *b.radius+|b.center| *a.radius+a.radius*b.radius) S+1⟩
def divNat (a : FixedBall) (n : ℕ) : FixedBall :=
  ⟨a.center/(n:ℤ),ceilDiv a.radius n+1⟩
def ofRat (S : ℕ) (q : ℚ) : FixedBall := ⟨⌊(S:ℚ)*q⌋,1⟩

lemma floor_div (a : ℤ) (n : ℕ) : ⌊(a:ℚ)/n⌋=a/(n:ℤ) := by
  rw [Int.floor_div_natCast, Int.floor_intCast]

lemma ceil_div (a : ℤ) (n : ℕ) : ⌈(a:ℚ)/n⌉=ceilDiv a n := by
  rw [show (a:ℚ)/n = -((-a:ℤ):ℚ)/n by push_cast; ring, neg_div, Int.ceil_neg]
  rw [floor_div]
  rfl

lemma toRational_zero (S : ℕ) : zero.toRational S=RationalBall.point 0 := by
  simp [toRational, zero, RationalBall.point]

lemma toRational_add (S : ℕ) (a b : FixedBall) :
    (add a b).toRational S=RationalBall.add (a.toRational S) (b.toRational S) := by
  simp [toRational, add, RationalBall.add, add_div]

lemma toRational_neg (S : ℕ) (a : FixedBall) :
    (neg a).toRational S=RationalBall.neg (a.toRational S) := by
  simp [toRational, neg, RationalBall.neg, neg_div]

lemma toRational_scale (S : ℕ) (k : ℤ) (a : FixedBall) :
    (scale k a).toRational S=RationalBall.mul (RationalBall.point k) (a.toRational S) := by
  simp [toRational, scale, RationalBall.mul, RationalBall.point, mul_div_assoc]

lemma toRational_mul {S : ℕ} (hS : 0<S) (a b : FixedBall) :
    (mul S a b).toRational S=RationalBall.roundedMul S (a.toRational S) (b.toRational S) := by
  have hs : (S:ℚ)≠0 := by positivity
  have habs : |(S:ℚ)|=(S:ℚ) := abs_of_nonneg (Nat.cast_nonneg S)
  unfold toRational mul RationalBall.roundedMul RationalBall.round RationalBall.mul
  congr 1
  · unfold RationalBall.roundedCenter
    rw [show (S:ℚ)*((a.center:ℚ)/S*((b.center:ℚ)/S))=(a.center*b.center:ℤ)/S by
      push_cast; field_simp, floor_div]
  · have hr : (S:ℚ)*
        (|(a.center:ℚ)/S| *((b.radius:ℚ)/S)+|(b.center:ℚ)/S| *((a.radius:ℚ)/S)+
          ((a.radius:ℚ)/S)*((b.radius:ℚ)/S)+1/S) =
        ((|a.center| *b.radius+|b.center| *a.radius+a.radius*b.radius:ℤ):ℚ)/S+1 := by
      rw [abs_div, abs_div, habs]
      push_cast
      field_simp
    rw [hr, Int.ceil_add_one, ceil_div]

lemma toRational_divNat {S : ℕ} (hS : 0<S) (a : FixedBall) (n : ℕ) :
    (divNat a n).toRational S=RationalBall.roundedDivNat S (a.toRational S) n := by
  have hs : (S:ℚ)≠0 := by positivity
  unfold toRational divNat RationalBall.roundedDivNat RationalBall.round RationalBall.divNat
  congr 1
  · unfold RationalBall.roundedCenter
    rw [show (S:ℚ)*((a.center:ℚ)/S/n)=(a.center:ℚ)/n by field_simp, floor_div]
  · rw [show (S:ℚ)*((a.radius:ℚ)/S/n+1/S)=(a.radius:ℚ)/n+1 by field_simp,
      Int.ceil_add_one, ceil_div]

theorem contains_zero (S : ℕ) : zero.Contains S 0 := by
  change (zero.toRational S).Contains 0
  rw [toRational_zero]
  simpa using RationalBall.contains_point 0

theorem contains_add {S : ℕ} {a b : FixedBall} {x y : ℝ}
    (hx : a.Contains S x) (hy : b.Contains S y) : (add a b).Contains S (x+y) := by
  change ((add a b).toRational S).Contains (x+y)
  rw [toRational_add]
  exact RationalBall.contains_add hx hy

theorem contains_neg {S : ℕ} {a : FixedBall} {x : ℝ}
    (hx : a.Contains S x) : (neg a).Contains S (-x) := by
  change ((neg a).toRational S).Contains (-x)
  rw [toRational_neg]
  exact RationalBall.contains_neg hx

theorem contains_scale {S : ℕ} (k : ℤ) {a : FixedBall} {x : ℝ}
    (hx : a.Contains S x) : (scale k a).Contains S ((k:ℝ)*x) := by
  change ((scale k a).toRational S).Contains ((k:ℝ)*x)
  rw [toRational_scale]
  simpa only [Rat.cast_intCast] using RationalBall.contains_mul (RationalBall.contains_point k) hx

theorem contains_mul {S : ℕ} (hS : 0<S) {a b : FixedBall} {x y : ℝ}
    (hx : a.Contains S x) (hy : b.Contains S y) : (mul S a b).Contains S (x*y) := by
  change ((mul S a b).toRational S).Contains (x*y)
  rw [toRational_mul hS]
  exact RationalBall.contains_roundedMul hS hx hy

theorem contains_divNat {S : ℕ} (hS : 0<S) {a : FixedBall} {x : ℝ}
    (hx : a.Contains S x) (n : ℕ) : (divNat a n).Contains S (x/n) := by
  change ((divNat a n).toRational S).Contains (x/n)
  rw [toRational_divNat hS]
  exact RationalBall.contains_roundedDivNat hS hx n

theorem contains_ofRat {S : ℕ} (hS : 0<S) (q : ℚ) : (ofRat S q).Contains S (q:ℝ) := by
  have hh := RationalBall.roundedCenter_bounds hS q
  have hq : |q-RationalBall.roundedCenter S q|≤1/(S:ℚ) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hh.1)]
    exact hh.2
  have hc := (Rat.cast_le (K:=ℝ)).mpr hq
  simpa [Contains, toRational, ofRat, RationalBall.Contains, RationalBall.roundedCenter] using hc

end FixedBall
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
  logInfo m!"Fixed-ball audit passed for {checked} declarations."


end
