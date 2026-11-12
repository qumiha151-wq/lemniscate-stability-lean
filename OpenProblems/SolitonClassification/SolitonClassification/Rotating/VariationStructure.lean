import SolitonClassification.Rotating.VariationTaylor
import SolitonClassification.Rotating.MatrixColumnNorm

/-! Exact structure of the complete six-dimensional variational polynomial.
These identities may support future sparse evaluation, but do not replace
any still-needed recurrence or tail checks for the other 25 entries. -/
namespace SolitonClassification.Rotating
noncomputable section
open Polynomial
set_option Elab.async false
set_option maxHeartbeats 1000000

theorem variationCoeff_b_row_succ (a v : State) (n : ℕ) :
    variationCoeff a v (n+1) 4=0 := by
  rw [variationCoeff]
  simp [variationRHS]

theorem variationPolynomial_b_row (a v : State) (N : ℕ) :
    variationPolynomial a v N 4=C (v 4) := by
  ext n
  rw [variationPolynomial_coeff]
  cases n with
  | zero => simp [variationCoeff_zero]
  | succ n => simp [variationCoeff_b_row_succ]

theorem variationRHS_theta_column (c : ℕ → State) (q : ℕ → ℝ) (n : ℕ) :
    variationRHS c q (fun j=>if j=0 then coordinateBasis 5 else 0) n=0 := by
  ext i
  fin_cases i <;> simp [variationRHS,realConvolution,ite_apply,coordinateBasis]

theorem variationCoeff_theta_column (a : State) (n : ℕ) :
    variationCoeff a (coordinateBasis 5) n=if n=0 then coordinateBasis 5 else 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [variationCoeff_zero]
    | succ n =>
      have he : variationRHS (taylorCoeff a) (squareCoeff (taylorCoeff a))
          (variationCoeff a (coordinateBasis 5)) n=0 := by
        rw [variationRHS_congr (taylorCoeff a) (taylorCoeff a)
          (squareCoeff (taylorCoeff a)) (squareCoeff (taylorCoeff a))
          (variationCoeff a (coordinateBasis 5)) (fun j=>if j=0 then coordinateBasis 5 else 0) n
          (by intros;rfl) (by intros;rfl) (fun j hj=>ih j (by omega))]
        exact variationRHS_theta_column _ _ n
      have hr:=variationCoeff_recurrence a (coordinateBasis 5) n
      rw [he] at hr
      have hz : variationCoeff a (coordinateBasis 5) (n+1)=0 :=
        (smul_eq_zero.mp hr).resolve_left (by positivity)
      simpa using hz

theorem variationPolynomial_theta_column (a : State) (N : ℕ) (i : Fin 6) :
    variationPolynomial a (coordinateBasis 5) N i=C (coordinateBasis 5 i) := by
  ext n
  rw [variationPolynomial_coeff,variationCoeff_theta_column]
  cases n <;> simp

theorem variationPolynomial_full_b_row (a : State) (N : ℕ) (j : Fin 6) :
    variationPolynomial a (coordinateBasis j) N 4=C (if (4:Fin 6)=j then 1 else 0) :=
  variationPolynomial_b_row a (coordinateBasis j) N

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.variationPolynomial_theta_column
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Complete variational b-row/theta-column structure audit passed for {count} declarations."
