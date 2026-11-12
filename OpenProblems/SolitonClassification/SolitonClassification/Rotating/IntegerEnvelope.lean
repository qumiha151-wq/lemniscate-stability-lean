import SolitonClassification.Rotating.PolynomialEnvelope
import Mathlib.Algebra.BigOperators.Field

/-! A proved common-denominator bridge. Concrete coefficient envelopes can
be checked with integer sums and powers, avoiding repeated rational gcd
normalization. The resulting interval bound has exactly the same semantics. -/
namespace SolitonClassification.Rotating
open Finset

def integerEnvelopeNumerator (b : ℕ → FixedBall) (base M : ℕ) : ℤ :=
  ∑n∈range (M+1),(|(b n).center|+(b n).radius)*(base:ℤ)^(M-n)

theorem fixedAbsUpper_common (S : ℕ) (b : FixedBall) :
    fixedAbsUpper S b=((|b.center|+b.radius:ℤ):ℚ)/S := by
  simp [fixedAbsUpper,FixedBall.toRational,abs_div,add_div]

theorem rationalEnvelope_common_denominator (A : ℕ → ℤ) {S base : ℕ}
    (hS : 0<S) (hb : 0<base) (M : ℕ) :
    rationalEnvelope (fun n=>(A n:ℚ)/S) (1/base) M=
      ((∑n∈range (M+1),A n*(base:ℤ)^(M-n):ℤ):ℚ)/((S:ℚ)*(base:ℚ)^M) := by
  have hs0 : (S:ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt hS
  have hb0 : (base:ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt hb
  unfold rationalEnvelope
  push_cast
  rw [sum_div]
  apply sum_congr rfl
  intro n hn
  have hn' : n≤M := by have := mem_range.mp hn; omega
  have hp : (base:ℚ)^(M-n)*(base:ℚ)^n=(base:ℚ)^M := by
    rw [←pow_add,Nat.sub_add_cancel hn']
  rw [div_pow,one_pow]
  field_simp [hs0,hb0]
  rw [←hp]
  ring

theorem fixedEnvelope_common_denominator (b : ℕ → FixedBall) {S base : ℕ}
    (hS : 0<S) (hb : 0<base) (M : ℕ) :
    rationalEnvelope (fun n=>fixedAbsUpper S (b n)) (1/base) M=
      (integerEnvelopeNumerator b base M:ℚ)/((S:ℚ)*(base:ℚ)^M) := by
  simp only [fixedAbsUpper_common]
  exact rationalEnvelope_common_denominator _ hS hb M

theorem fixedEnvelope_le_of_integer_check (b : ℕ → FixedBall) {S base M : ℕ} {K : ℤ} {B : ℚ}
    (hS : 0<S) (hb : 0<base) (hnum : integerEnvelopeNumerator b base M≤K)
    (hquot : (K:ℚ)/((S:ℚ)*(base:ℚ)^M)≤B) :
    rationalEnvelope (fun n=>fixedAbsUpper S (b n)) (1/base) M≤B := by
  rw [fixedEnvelope_common_denominator b hS hb M]
  apply le_trans _ hquot
  apply div_le_div_of_nonneg_right
  · exact_mod_cast hnum
  · positivity

end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.fixedEnvelope_le_of_integer_check
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Integer common-denominator envelope audit passed."
