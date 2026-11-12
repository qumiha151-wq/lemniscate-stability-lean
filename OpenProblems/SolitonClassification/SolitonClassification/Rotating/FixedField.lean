import SolitonClassification.Rotating.FixedBall
import SolitonClassification.Rotating.Field

/-! Integer-ball evaluation of the actual field. The Euler output is a
polynomial, not an asserted ODE enclosure or an assumed valid CAP report. -/
namespace SolitonClassification.Rotating

abbrev BallState := Fin 6 → FixedBall

def fixedField (S : ℕ) (z : BallState) : BallState := fun i => match i.val with
  | 0 => FixedBall.scale 8 (z 1)
  | 1 => FixedBall.add
      (FixedBall.neg (FixedBall.divNat (FixedBall.mul S (FixedBall.mul S (z 0) (z 0)) (z 0)) 16))
      (FixedBall.add (FixedBall.neg (FixedBall.divNat (z 2) 8))
        (FixedBall.neg (FixedBall.divNat (FixedBall.mul S (z 4) (z 3)) 8)))
  | 2 => FixedBall.neg (FixedBall.mul S (z 0) (z 3))
  | 3 => FixedBall.add (FixedBall.ofRat S 1) (FixedBall.mul S (z 0) (z 2))
  | 4 => FixedBall.zero
  | _ => z 0

theorem fixedField_contains {S : ℕ} (hS : 0<S) {z : BallState} {a : State}
    (ha : ∀i,(z i).Contains S (a i)) (i : Fin 6) :
    (fixedField S z i).Contains S (field a i) := by
  fin_cases i
  · simpa [fixedField,field] using FixedBall.contains_scale 8 (ha 1)
  · have hcube := FixedBall.contains_mul hS (FixedBall.contains_mul hS (ha 0) (ha 0)) (ha 0)
    have h := FixedBall.contains_add
      (FixedBall.contains_neg (FixedBall.contains_divNat hS hcube 16))
      (FixedBall.contains_add (FixedBall.contains_neg (FixedBall.contains_divNat hS (ha 2) 8))
        (FixedBall.contains_neg (FixedBall.contains_divNat hS
          (FixedBall.contains_mul hS (ha 4) (ha 3)) 8)))
    simpa [fixedField,field,pow_succ,pow_two,sub_eq_add_neg,add_assoc,neg_div] using h
  · simpa [fixedField,field,neg_mul] using
      FixedBall.contains_neg (FixedBall.contains_mul hS (ha 0) (ha 3))
  · simpa [fixedField,field] using FixedBall.contains_add
      (FixedBall.contains_ofRat hS 1) (FixedBall.contains_mul hS (ha 0) (ha 2))
  · simpa [fixedField,field] using FixedBall.contains_zero S
  · exact ha 0

def fixedEuler (S : ℕ) (h : ℚ) (z : BallState) : BallState := fun i =>
  FixedBall.add (z i) (FixedBall.mul S (FixedBall.ofRat S h) (fixedField S z i))

theorem fixedEuler_contains {S : ℕ} (hS : 0<S) (h : ℚ) {z : BallState} {a : State}
    (ha : ∀i,(z i).Contains S (a i)) (i : Fin 6) :
    (fixedEuler S h z i).Contains S ((a+(h:ℝ) • field a) i) := by
  exact FixedBall.contains_add (ha i) (FixedBall.contains_mul hS
    (FixedBall.contains_ofRat hS h) (fixedField_contains hS ha i))

theorem fixedBall_contains_lower_upper {S : ℕ} {b : FixedBall} {x : ℝ}
    (hx : b.Contains S x) :
    ((b.toRational S).center:ℝ)-(b.toRational S).radius≤x ∧
      x≤((b.toRational S).center:ℝ)+(b.toRational S).radius := by
  change |x-((b.toRational S).center:ℝ)|≤((b.toRational S).radius:ℝ) at hx
  rcases abs_le.mp hx with ⟨hl,hu⟩
  constructor <;> linarith

end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.fixedField_contains
#print axioms SolitonClassification.Rotating.fixedEuler_contains

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
  logInfo "Rotating fixed-field/evaluation audit passed; standard axioms only."
