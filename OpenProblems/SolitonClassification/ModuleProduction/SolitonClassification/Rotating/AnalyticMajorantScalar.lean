module

public import SolitonClassification.Rotating.TaylorCoefficients
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

/-! A finite, arbitrary-order scalar majorant for the rotating field.
All coefficients and residual cancellation are proved here independently.
No cross-problem imports, numerical oracle, or infinite-series assumption.
The constants correspond to 61*(1+w/(19/2))^3. -/
namespace SolitonClassification.Rotating.UniversalMajorant
noncomputable section
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def rate : ℝ := 122/19

def linearMajorantResidual (u : ℝ[X]) : ℝ[X] :=
  (1-C (2*rate)*X)*derivative u-C rate*u

lemma coeff_X_derivative (u : ℝ[X]) (n : ℕ) :
    (X*derivative u).coeff n = (n:ℝ)*u.coeff n := by
  cases n with
  | zero => simp
  | succ n => rw [coeff_X_mul, coeff_derivative]; push_cast; ring

lemma linearMajorantResidual_coeff (u : ℝ[X]) (n : ℕ) :
    (linearMajorantResidual u).coeff n =
      (n+1:ℝ)*u.coeff (n+1)-rate*(2*n+1)*u.coeff n := by
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
    derivative ((1-C (2*rate)*X)*u^2) = C 2*u*linearMajorantResidual u := by
  simp [linearMajorantResidual, derivative_mul, derivative_pow, C_mul, C_ofNat]
  ring

lemma square_defect_coeff_zero {u : ℝ[X]} {N : ℕ}
    (hu0 : u.coeff 0 = 1)
    (hlin : ∀ n < N, (linearMajorantResidual u).coeff n = 0) :
    ∀ n ≤ N, (((1-C (2*rate)*X)*u^2)-1).coeff n = 0 := by
  intro n hn
  cases n with
  | zero => simp [pow_two, hu0]
  | succ n =>
    have hd : (derivative ((1-C (2*rate)*X)*u^2)).coeff n = 0 := by
      rw [majorant_square_derivative_identity]
      exact coeff_mul_zero_below hlin (by omega)
    rw [coeff_derivative] at hd
    have hc : (((1-C (2*rate)*X)*u^2)).coeff (n+1) = 0 := by
      exact (mul_eq_zero.mp hd).resolve_right (by positivity)
    simpa [coeff_sub, coeff_one] using hc

lemma cubic_defect_identity (u : ℝ[X]) :
    (1-C (2*rate)*X)*(derivative u-C rate*u^3) = linearMajorantResidual u-
      C rate*u*(((1-C (2*rate)*X)*u^2)-1) := by
  unfold linearMajorantResidual
  ring

theorem cubic_defect_coeff_zero {u : ℝ[X]} {N : ℕ}
    (hu0 : u.coeff 0 = 1)
    (hlin : ∀ n < N, (linearMajorantResidual u).coeff n = 0) :
    ∀ n < N, (derivative u-C rate*u^3).coeff n = 0 := by
  have hs := square_defect_coeff_zero hu0 hlin
  have hprod : ∀ n < N, ((1-C (2*rate)*X)*(derivative u-C rate*u^3)).coeff n = 0 := by
    intro n hn
    rw [cubic_defect_identity, coeff_sub, hlin n hn]
    have hh : (C rate*u*(((1-C (2*rate)*X)*u^2)-1)).coeff n = 0 :=
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
    simp only [hi, mul_zero, sub_zero] at hh
    exact hh

def scalarCoeff : ℕ → ℚ
  | 0 => 1
  | n+1 => (122/19)*(2*n+1)/(n+1)*scalarCoeff n

lemma scalarCoeff_nonneg (n : ℕ) : 0≤scalarCoeff n := by
  induction n with
  | zero => norm_num [scalarCoeff]
  | succ n ih => simp only [scalarCoeff]; positivity

lemma scalarCoeff_recurrence (n : ℕ) :
    (n+1:ℝ)*(scalarCoeff (n+1):ℝ)=rate*(2*n+1)*(scalarCoeff n:ℝ) := by
  simp only [scalarCoeff, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_add, Rat.cast_natCast, rate]
  push_cast
  field_simp

def scalarPolynomial (N : ℕ) : ℝ[X] :=
  ∑ n ∈ Finset.range (N+1), monomial n (scalarCoeff n : ℝ)

lemma scalarPolynomial_coeff (N n : ℕ) :
    (scalarPolynomial N).coeff n=if n≤N then (scalarCoeff n:ℝ) else 0 := by
  simp [scalarPolynomial,coeff_monomial,Finset.mem_range]

lemma scalarPolynomial_zero (N : ℕ) : (scalarPolynomial N).coeff 0=1 := by
  simp [scalarPolynomial_coeff,scalarCoeff]

lemma scalarPolynomial_nonneg (N n : ℕ) : 0≤(scalarPolynomial N).coeff n := by
  rw [scalarPolynomial_coeff]
  split_ifs
  · exact_mod_cast scalarCoeff_nonneg n
  · exact le_rfl

lemma scalarPolynomial_linear_zero (N n : ℕ) (hn : n<N) :
    (linearMajorantResidual (scalarPolynomial N)).coeff n=0 := by
  rw [linearMajorantResidual_coeff,scalarPolynomial_coeff,scalarPolynomial_coeff,
    if_pos (by omega),if_pos (by omega),scalarCoeff_recurrence]
  ring

def displacementPolynomial (N : ℕ) : ℝ[X] := C (19/2)*(scalarPolynomial N-1)

lemma displacementPolynomial_zero (N : ℕ) :
    (displacementPolynomial N).coeff 0=0 := by
  simp [displacementPolynomial,scalarPolynomial_zero]

lemma displacementPolynomial_pos (N n : ℕ) (hn : 0<n) :
    (displacementPolynomial N).coeff n=(19/2)*(scalarPolynomial N).coeff n := by
  simp [displacementPolynomial,coeff_sub,coeff_one,ne_of_gt hn]

lemma displacementPolynomial_nonneg (N n : ℕ) :
    0≤(displacementPolynomial N).coeff n := by
  by_cases hn : n=0
  · simp [hn,displacementPolynomial_zero]
  · rw [displacementPolynomial_pos N n (Nat.pos_of_ne_zero hn)]
    exact mul_nonneg (by norm_num) (scalarPolynomial_nonneg N n)

def scalarForcing (w : ℝ[X]) : ℝ[X] :=
  C 61+C (366/19)*w+C (732/361)*w^2+C (488/6859)*w^3

lemma scalarForcing_eq (N : ℕ) :
    scalarForcing (displacementPolynomial N)=C 61*(scalarPolynomial N)^3 := by
  have h1 : (C (366/19):ℝ[X])*C (19/2)=C 183 := by
    rw [←C_mul]; norm_num
  have h2 : (C (732/361):ℝ[X])*C (19/2)^2=C 183 := by
    rw [←C_pow,←C_mul]; norm_num
  have h3 : (C (488/6859):ℝ[X])*C (19/2)^3=C 61 := by
    rw [←C_pow,←C_mul]; norm_num
  simp only [scalarForcing,displacementPolynomial,mul_pow,←mul_assoc,h1,h2,h3]
  simp only [C_ofNat]
  ring

def scalarResidual (N : ℕ) : ℝ[X] :=
  C 61*(scalarPolynomial N)^3-derivative (displacementPolynomial N)

lemma scalarResidual_low (N n : ℕ) (hn : n<N) :
    (scalarResidual N).coeff n=0 := by
  have hh := cubic_defect_coeff_zero (scalarPolynomial_zero N)
    (scalarPolynomial_linear_zero N) n hn
  simp only [coeff_sub,coeff_C_mul,coeff_derivative] at hh
  simp only [scalarResidual,coeff_sub,coeff_C_mul,coeff_derivative]
  rw [displacementPolynomial_pos N (n+1) (by omega)]
  dsimp [rate] at hh
  linarith

lemma scalarForcing_recurrence (N n : ℕ) (hn : n<N) :
    (scalarForcing (displacementPolynomial N)).coeff n=
      (n+1:ℝ)*(displacementPolynomial N).coeff (n+1) := by
  have hh := scalarResidual_low N n hn
  simpa only [scalarForcing_eq,scalarResidual,coeff_sub,coeff_C_mul,
    coeff_derivative,sub_eq_zero,mul_comm] using hh

lemma scalarResidual_nonneg (N n : ℕ) : 0≤(scalarResidual N).coeff n := by
  by_cases hn : n<N
  · rw [scalarResidual_low N n hn]
  · have hd : (derivative (displacementPolynomial N)).coeff n=0 := by
      rw [coeff_derivative,displacementPolynomial_pos N (n+1) (by omega),
        scalarPolynomial_coeff,if_neg (by omega),mul_zero,zero_mul]
    simp only [scalarResidual,coeff_sub,coeff_C_mul,hd,sub_zero]
    have hu2 := coeff_mul_nonneg_all (scalarPolynomial_nonneg N) (scalarPolynomial_nonneg N)
    have hu3 := coeff_mul_nonneg_all hu2 (scalarPolynomial_nonneg N) n
    have he : (scalarPolynomial N)^3=scalarPolynomial N*scalarPolynomial N*scalarPolynomial N := by ring
    rw [he]
    positivity

lemma eval_nonneg_of_coeff_nonneg {p : ℝ[X]} (hp : ∀ n,0≤p.coeff n)
    {s : ℝ} (hs : 0≤s) : 0≤p.eval s := by
  rw [eval_eq_sum,Polynomial.sum]
  exact Finset.sum_nonneg fun n _=>mul_nonneg (hp n) (pow_nonneg hs n)

lemma eval_monotone_of_coeff_nonneg {p : ℝ[X]} (hp : ∀ n,0≤p.coeff n)
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) : p.eval s≤p.eval t := by
  rw [eval_eq_sum,eval_eq_sum,Polynomial.sum,Polynomial.sum]
  exact Finset.sum_le_sum fun n _=>mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst n) (hp n)

theorem scalarResidual_uniform (N : ℕ) {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    0≤(scalarResidual N).eval s ∧ (scalarResidual N).eval s≤(scalarResidual N).eval t :=
  ⟨eval_nonneg_of_coeff_nonneg (scalarResidual_nonneg N) hs,
    eval_monotone_of_coeff_nonneg (scalarResidual_nonneg N) hs hst⟩

end
end SolitonClassification.Rotating.UniversalMajorant

#print axioms SolitonClassification.Rotating.UniversalMajorant.scalarResidual_uniform

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (←collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked+1
  logInfo m!"Universal scalar majorant audit passed: {checked} declarations; standard axioms only."

end
