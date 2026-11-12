import CentroidEscape.PolynomialResidual
import CentroidEscape.PolynomialEvaluation
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic.Ring

namespace CentroidEscape
noncomputable section
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def linearMajorantResidual (u : ℝ[X]) : ℝ[X] :=
  (1-C 12*X)*derivative u-C 6*u

lemma coeff_X_derivative (u : ℝ[X]) (n : ℕ) :
    (X*derivative u).coeff n = (n:ℝ)*u.coeff n := by
  cases n with
  | zero => simp
  | succ n => rw [coeff_X_mul, coeff_derivative]; push_cast; ring

lemma linearMajorantResidual_coeff (u : ℝ[X]) (n : ℕ) :
    (linearMajorantResidual u).coeff n =
      (n+1:ℝ)*u.coeff (n+1)-6*(2*n+1)*u.coeff n := by
  simp only [linearMajorantResidual, sub_mul, one_mul, mul_assoc,
    coeff_sub, coeff_C_mul, coeff_X_derivative, coeff_derivative]
  ring

lemma coeff_mul_zero_below {p q : ℝ[X]} {N : ℕ}
    (hq : ∀ n < N, q.coeff n = 0) {n : ℕ} (hn : n < N) : (p*q).coeff n = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have he := Finset.mem_antidiagonal.mp hij
  rw [hq ij.2 (by omega), mul_zero]

lemma coeff_mul_nonneg_all {p q : ℝ[X]}
    (hp : ∀ n, 0 ≤ p.coeff n) (hq : ∀ n, 0 ≤ q.coeff n) (n : ℕ) :
    0 ≤ (p*q).coeff n := by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun ij _ => mul_nonneg (hp _) (hq _)

lemma majorant_square_derivative_identity (u : ℝ[X]) :
    derivative ((1-C 12*X)*u^2) = C 2*u*linearMajorantResidual u := by
  simp [linearMajorantResidual, derivative_mul, derivative_pow, C_ofNat]
  ring

lemma square_defect_coeff_zero {u : ℝ[X]} {N : ℕ}
    (hu0 : u.coeff 0 = 1)
    (hlin : ∀ n < N, (linearMajorantResidual u).coeff n = 0) :
    ∀ n ≤ N, (((1-C 12*X)*u^2)-1).coeff n = 0 := by
  intro n hn
  cases n with
  | zero => simp [pow_two, hu0]
  | succ n =>
    have hd : (derivative ((1-C 12*X)*u^2)).coeff n = 0 := by
      rw [majorant_square_derivative_identity]
      exact coeff_mul_zero_below hlin (by omega)
    rw [coeff_derivative] at hd
    have hc : (((1-C 12*X)*u^2)).coeff (n+1) = 0 := by
      exact (mul_eq_zero.mp hd).resolve_right (by positivity)
    simpa [coeff_sub, coeff_one] using hc

lemma cubic_defect_identity (u : ℝ[X]) :
    (1-C 12*X)*(derivative u-C 6*u^3) = linearMajorantResidual u-
      C 6*u*(((1-C 12*X)*u^2)-1) := by
  unfold linearMajorantResidual
  ring

theorem cubic_defect_coeff_zero {u : ℝ[X]} {N : ℕ}
    (hu0 : u.coeff 0 = 1)
    (hlin : ∀ n < N, (linearMajorantResidual u).coeff n = 0) :
    ∀ n < N, (derivative u-C 6*u^3).coeff n = 0 := by
  have hs := square_defect_coeff_zero hu0 hlin
  have hprod : ∀ n < N, ((1-C 12*X)*(derivative u-C 6*u^3)).coeff n = 0 := by
    intro n hn
    rw [cubic_defect_identity, coeff_sub, hlin n hn]
    have hh : (C 6*u*(((1-C 12*X)*u^2)-1)).coeff n = 0 :=
      coeff_mul_zero_below (N := N) (fun j hj => hs j hj.le) hn
    rw [hh, sub_self]
  intro n hn
  induction n with
  | zero => simpa [sub_mul, mul_assoc] using hprod 0 hn
  | succ n ih =>
    have hh := hprod (n+1) hn
    have hi := ih (by omega)
    simp only [sub_mul, one_mul, mul_assoc, coeff_sub, coeff_C_mul, coeff_X_mul] at hh
    simp only [coeff_sub, coeff_C_mul] at hi ⊢
    rw [hi, mul_zero, sub_zero] at hh
    exact hh

def scalarMajorant : ℝ[X] :=
  ∑ n ∈ Finset.range 161, monomial n (majorantCoeff n : ℝ)

lemma scalarMajorant_coeff (n : ℕ) :
    scalarMajorant.coeff n = if n < 161 then (majorantCoeff n : ℝ) else 0 := by
  simp [scalarMajorant, coeff_monomial, Finset.mem_range]

lemma scalarMajorant_coeff_zero : scalarMajorant.coeff 0 = 1 := by
  rw [scalarMajorant_coeff]
  simp [majorantCoeff_zero]

lemma scalarMajorant_coeff_nonneg (n : ℕ) : 0 ≤ scalarMajorant.coeff n := by
  rw [scalarMajorant_coeff]
  split_ifs <;> positivity

lemma scalarMajorant_linear_residual_zero (n : ℕ) (hn : n < 160) :
    (linearMajorantResidual scalarMajorant).coeff n = 0 := by
  rw [linearMajorantResidual_coeff, scalarMajorant_coeff, scalarMajorant_coeff,
    if_pos (by omega : n+1 < 161), if_pos (by omega : n < 161)]
  have hh := majorantCoeff_recurrence ⟨n, hn⟩
  have hr : (n+1:ℝ)*(majorantCoeff (n+1):ℝ) =
      6*(2*n+1)*(majorantCoeff n:ℝ) := by exact_mod_cast hh
  linarith

def scalarResidual : ℝ[X] := C 2*scalarMajorant^3-C (1/3)*derivative scalarMajorant

theorem scalarResidual_low_coeff_zero (n : ℕ) (hn : n < 160) :
    scalarResidual.coeff n = 0 := by
  have hh := cubic_defect_coeff_zero scalarMajorant_coeff_zero
    scalarMajorant_linear_residual_zero n hn
  simp only [coeff_sub, coeff_C_mul] at hh
  simp only [scalarResidual, coeff_sub, coeff_C_mul]
  linarith

theorem scalarResidual_coeff_nonneg (n : ℕ) : 0 ≤ scalarResidual.coeff n := by
  by_cases hn : n < 160
  · rw [scalarResidual_low_coeff_zero n hn]
  · have hd : (derivative scalarMajorant).coeff n = 0 := by
      rw [coeff_derivative, scalarMajorant_coeff, if_neg (by omega), zero_mul]
    simp only [scalarResidual, coeff_sub, coeff_C_mul, hd, mul_zero, sub_zero]
    have hu2 : ∀ k, 0 ≤ (scalarMajorant*scalarMajorant).coeff k :=
      coeff_mul_nonneg_all scalarMajorant_coeff_nonneg scalarMajorant_coeff_nonneg
    have hu3 := coeff_mul_nonneg_all hu2 scalarMajorant_coeff_nonneg n
    have hp : scalarMajorant^3 = scalarMajorant*scalarMajorant*scalarMajorant := by ring
    rw [hp]
    positivity

lemma eval_nonneg_of_coeff_nonneg {p : ℝ[X]} (hp : ∀ n, 0 ≤ p.coeff n)
    {s : ℝ} (hs : 0 ≤ s) : 0 ≤ p.eval s := by
  rw [eval_eq_sum, Polynomial.sum]
  exact Finset.sum_nonneg fun n _ => mul_nonneg (hp n) (pow_nonneg hs n)

lemma eval_monotone_of_coeff_nonneg {p : ℝ[X]} (hp : ∀ n, 0 ≤ p.coeff n)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : p.eval s ≤ p.eval t := by
  rw [eval_eq_sum, eval_eq_sum, Polynomial.sum, Polynomial.sum]
  apply Finset.sum_le_sum
  intro n hn
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst n) (hp n)

theorem scalarResidual_bounds {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    0 ≤ scalarResidual.eval s ∧ scalarResidual.eval s ≤ scalarResidual.eval t := by
  exact ⟨eval_nonneg_of_coeff_nonneg scalarResidual_coeff_nonneg hs,
    eval_monotone_of_coeff_nonneg scalarResidual_coeff_nonneg hs hst⟩

theorem scalarMajorant_eval (s : ℝ) : scalarMajorant.eval s = majorantPoly s := by
  simp [scalarMajorant, majorantPoly, eval_finsetSum]

theorem scalarMajorant_derivative_eval (s : ℝ) :
    (derivative scalarMajorant).eval s = majorantPolyDeriv s := by
  simp [scalarMajorant, majorantPolyDeriv, derivative_monomial, eval_finsetSum]

theorem scalarResidual_eval (s : ℝ) :
    scalarResidual.eval s = 2*(majorantPoly s)^3-deriv majorantPoly s/3 := by
  rw [(majorantPoly_hasDerivAt s).deriv]
  simp only [scalarResidual, eval_sub, eval_mul, eval_C, eval_pow,
    scalarMajorant_eval, scalarMajorant_derivative_eval]
  ring

theorem scalarResidual_value : scalarResidual.eval (1/100) = (polynomialResidual:ℝ) := by
  rw [scalarResidual_eval]
  exact polynomialResidual_is_derivative_residual

theorem finite_majorant_residual_uniform {s : ℝ} (hs : 0 ≤ s) (hst : s ≤ 1/100) :
    0 ≤ 2*(majorantPoly s)^3-deriv majorantPoly s/3 ∧
      2*(majorantPoly s)^3-deriv majorantPoly s/3 ≤ (polynomialResidual:ℝ) := by
  have hh := scalarResidual_bounds hs hst
  rwa [scalarResidual_eval, scalarResidual_value] at hh

theorem finite_majorant_residual_abs {s : ℝ} (hs : 0 ≤ s) (hst : s ≤ 1/100) :
    |deriv majorantPoly s/3-2*(majorantPoly s)^3| ≤ (polynomialResidual:ℝ) := by
  have hh := finite_majorant_residual_uniform hs hst
  rw [abs_sub_comm, abs_of_nonneg hh.1]
  exact hh.2

theorem finite_majorant_excursion_uniform {s : ℝ} (hs : 0 ≤ s) (hst : s ≤ 1/100) :
    0 ≤ (majorantPoly s-1)/3 ∧ (majorantPoly s-1)/3 < 23/1000 := by
  have hlo := eval_monotone_of_coeff_nonneg scalarMajorant_coeff_nonneg
    (show (0:ℝ) ≤ 0 from le_rfl) hs
  rw [← coeff_zero_eq_eval_zero, scalarMajorant_coeff_zero, scalarMajorant_eval] at hlo
  have hhi := eval_monotone_of_coeff_nonneg scalarMajorant_coeff_nonneg hs hst
  simp only [scalarMajorant_eval, majorantPoly_value] at hhi
  have hbound : ((majorantValue:ℝ)-1)/3 < (23/1000:ℝ) := by
    have hh := (Rat.cast_lt (K := ℝ)).2 majorant_excursion_bound
    norm_num at hh ⊢
    exact hh
  constructor <;> linarith

end
end CentroidEscape

#print axioms CentroidEscape.scalarResidual_bounds
#print axioms CentroidEscape.finite_majorant_residual_uniform

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
  logInfo m!"Scalar-majorant audit passed for {checked} declarations."
