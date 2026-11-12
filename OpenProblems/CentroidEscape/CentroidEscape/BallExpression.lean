import CentroidEscape.RationalBall
import CentroidEscape.WeightedField

/-!
# A checked finite rational-expression evaluator

The numerical evaluator has no real-number oracle. Its correctness theorem
relates its outward-rounded rational balls to the real expression semantics.
The concrete seven-coordinate shooting field is an explicit application.
-/
namespace CentroidEscape

inductive BallExpression where
  | const : ℚ → BallExpression
  | var : ℕ → BallExpression
  | add : BallExpression → BallExpression → BallExpression
  | neg : BallExpression → BallExpression
  | mul : BallExpression → BallExpression → BallExpression
  | divNat : BallExpression → ℕ → BallExpression

namespace BallExpression

def evalBall (S : ℕ) (env : ℕ → RationalBall) : BallExpression → RationalBall
  | const q => RationalBall.point q
  | var n => env n
  | add a b => RationalBall.roundedAdd S (evalBall S env a) (evalBall S env b)
  | neg a => RationalBall.neg (evalBall S env a)
  | mul a b => RationalBall.roundedMul S (evalBall S env a) (evalBall S env b)
  | divNat a n => RationalBall.roundedDivNat S (evalBall S env a) n

noncomputable def evalReal (env : ℕ → ℝ) : BallExpression → ℝ
  | const q => q
  | var n => env n
  | add a b => evalReal env a + evalReal env b
  | neg a => -evalReal env a
  | mul a b => evalReal env a * evalReal env b
  | divNat a n => evalReal env a / n

theorem evalBall_contains {S : ℕ} (hS : 0 < S)
    {balls : ℕ → RationalBall} {values : ℕ → ℝ}
    (henv : ∀ i, (balls i).Contains (values i)) (e : BallExpression) :
    (evalBall S balls e).Contains (evalReal values e) := by
  induction e with
  | const q => exact RationalBall.contains_point q
  | var n => exact henv n
  | add a b ha hb => exact RationalBall.contains_roundedAdd hS ha hb
  | neg a ha => exact RationalBall.contains_neg ha
  | mul a b ha hb => exact RationalBall.contains_roundedMul hS ha hb
  | divNat a n ha => exact RationalBall.contains_roundedDivNat hS ha n

end BallExpression

open BallExpression in
def weightedFieldExpression : Fin 7 → BallExpression :=
  ![mul (const 4) (var 2),
    mul (const 4) (var 3),
    neg (mul (const 16) (mul (var 4) (var 3))),
    mul (const 16) (mul (var 4) (var 2)),
    mul (const 4) (var 5),
    add (neg (mul (const 32) (mul (mul (var 4) (var 4)) (var 4))))
      (divNat (add (mul (var 0) (var 3)) (neg (mul (var 1) (var 2)))) 16),
    var 0]

noncomputable def weightedRealEnv (a : WeightedState) (n : ℕ) : ℝ :=
  if hn : n < 7 then a ⟨n,hn⟩ else 0

def weightedBallEnv (a : Fin 7 → RationalBall) (n : ℕ) : RationalBall :=
  if hn : n < 7 then a ⟨n,hn⟩ else RationalBall.point 0

theorem weightedFieldExpression_correct (a : WeightedState) (i : Fin 7) :
    BallExpression.evalReal (weightedRealEnv a) (weightedFieldExpression i) = weightedField a i := by
  fin_cases i <;> norm_num [weightedFieldExpression, BallExpression.evalReal, weightedRealEnv,
    weightedField] <;>
    simp only [show (⟨2, by decide⟩ : Fin 7) = 2 from rfl,
      show (⟨3, by decide⟩ : Fin 7) = 3 from rfl,
      show (⟨4, by decide⟩ : Fin 7) = 4 from rfl,
      show (⟨5, by decide⟩ : Fin 7) = 5 from rfl] <;> ring

def evaluateWeightedField (S : ℕ) (a : Fin 7 → RationalBall) (i : Fin 7) : RationalBall :=
  BallExpression.evalBall S (weightedBallEnv a) (weightedFieldExpression i)

theorem evaluateWeightedField_contains {S : ℕ} (hS : 0 < S)
    {balls : Fin 7 → RationalBall} {a : WeightedState}
    (ha : ∀ i, (balls i).Contains (a i)) (i : Fin 7) :
    (evaluateWeightedField S balls i).Contains (weightedField a i) := by
  have he : ∀ n, (weightedBallEnv balls n).Contains (weightedRealEnv a n) := by
    intro n
    unfold weightedBallEnv weightedRealEnv
    split_ifs with hn
    · exact ha ⟨n,hn⟩
    · simpa using RationalBall.contains_point 0
  have hh := BallExpression.evalBall_contains hS he (weightedFieldExpression i)
  rwa [weightedFieldExpression_correct] at hh

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
  logInfo m!"Ball-expression audit passed: {checked} declarations; standard axioms only."
