import SolitonClassification.Rotating.AnalyticMajorantScalar
import Mathlib.Algebra.Polynomial.Roots

/-! Arbitrary finite Jacobian majorants. The coefficients are those of U^3,
proved by finite linear residual cancellation; no infinite series is used.
State order M may exceed the variational order N. -/
namespace SolitonClassification.Rotating.UniversalMajorant
noncomputable section
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def jacCoeff (n : ℕ) : ℚ := (2*(n:ℚ)+1)*scalarCoeff n

lemma jacCoeff_nonneg (n : ℕ) : 0≤jacCoeff n := by
  unfold jacCoeff
  exact mul_nonneg (by positivity) (scalarCoeff_nonneg n)

lemma jacCoeff_recurrence (n : ℕ) :
    (n+1:ℝ)*(jacCoeff (n+1):ℝ)=rate*(2*n+3)*(jacCoeff n:ℝ) := by
  simp only [jacCoeff,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,Rat.cast_ofNat]
  push_cast
  calc
    _ = (2*(n:ℝ)+3)*((n+1)*(scalarCoeff (n+1):ℝ)) := by ring
    _ = (2*(n:ℝ)+3)*(rate*(2*n+1)*(scalarCoeff n:ℝ)) := by
      rw [scalarCoeff_recurrence]
    _ = _ := by ring

def jacPolynomial (N : ℕ) : ℝ[X] :=
  ∑ n ∈ Finset.range (N+1),monomial n (jacCoeff n:ℝ)

lemma jacPolynomial_coeff (N n : ℕ) :
    (jacPolynomial N).coeff n=if n≤N then (jacCoeff n:ℝ) else 0 := by
  simp [jacPolynomial,coeff_monomial,Finset.mem_range]

lemma jacPolynomial_zero (N : ℕ) : (jacPolynomial N).coeff 0=1 := by
  simp [jacPolynomial_coeff,jacCoeff,scalarCoeff]

lemma jacPolynomial_nonneg (N n : ℕ) : 0≤(jacPolynomial N).coeff n := by
  rw [jacPolynomial_coeff]
  split_ifs
  · exact_mod_cast jacCoeff_nonneg n
  · exact le_rfl

def linearJacResidual (v : ℝ[X]) : ℝ[X] :=
  (1-C (2*rate)*X)*derivative v-C (3*rate)*v

lemma linearJacResidual_coeff (v : ℝ[X]) (n : ℕ) :
    (linearJacResidual v).coeff n=
      (n+1:ℝ)*v.coeff (n+1)-rate*(2*n+3)*v.coeff n := by
  simp only [linearJacResidual,sub_mul,one_mul,mul_assoc,
    coeff_sub,coeff_C_mul,coeff_X_derivative,coeff_derivative]
  ring

lemma jacPolynomial_linear_zero (N n : ℕ) (hn : n<N) :
    (linearJacResidual (jacPolynomial N)).coeff n=0 := by
  rw [linearJacResidual_coeff,jacPolynomial_coeff,jacPolynomial_coeff,
    if_pos (by omega),if_pos (by omega),jacCoeff_recurrence]
  ring

def jacLipschitzPolynomial (M : ℕ) : ℝ[X] := C (3*rate)*(scalarPolynomial M)^2

lemma jacLipschitzPolynomial_nonneg (M n : ℕ) :
    0≤(jacLipschitzPolynomial M).coeff n := by
  simp only [jacLipschitzPolynomial,coeff_C_mul,pow_two]
  exact mul_nonneg (by norm_num [rate])
    (coeff_mul_nonneg_all (scalarPolynomial_nonneg M) (scalarPolynomial_nonneg M) n)

lemma jacLipschitzPolynomial_displacement (M : ℕ) :
    jacLipschitzPolynomial M=C (366/19)+C (1464/361)*displacementPolynomial M+
      C (1464/6859)*(displacementPolynomial M)^2 := by
  apply Polynomial.funext
  intro t
  simp only [jacLipschitzPolynomial,displacementPolynomial,rate,eval_add,eval_mul,
    eval_C,eval_pow,eval_sub,eval_one]
  ring

def jacResidual (M N : ℕ) : ℝ[X] :=
  jacLipschitzPolynomial M*jacPolynomial N-derivative (jacPolynomial N)

lemma jac_defect_identity (u v : ℝ[X]) :
    (1-C (2*rate)*X)*(derivative v-C (3*rate)*u^2*v)=
      linearJacResidual v-C (3*rate)*v*(((1-C (2*rate)*X)*u^2)-1) := by
  unfold linearJacResidual
  ring

/-- The finite mixed-order Jacobi recurrence has no low-order defect. -/
theorem jacResidual_low (M N n : ℕ) (hNM : N≤M) (hn : n<N) :
    (jacResidual M N).coeff n=0 := by
  let u := scalarPolynomial M
  let v := jacPolynomial N
  have hs : ∀ j<N, (((1-C (2*rate)*X)*u^2)-1).coeff j=0 := by
    intro j hj
    exact square_defect_coeff_zero (scalarPolynomial_zero M)
      (scalarPolynomial_linear_zero M) j (by omega)
  have hprod : ∀ j<N,
      ((1-C (2*rate)*X)*(derivative v-C (3*rate)*u^2*v)).coeff j=0 := by
    intro j hj
    rw [jac_defect_identity,coeff_sub,jacPolynomial_linear_zero N j hj]
    have hh : (C (3*rate)*v*(((1-C (2*rate)*X)*u^2)-1)).coeff j=0 :=
      coeff_mul_zero_below hs hj
    rw [hh,sub_self]
  have hz : ∀ j<N, (derivative v-C (3*rate)*u^2*v).coeff j=0 := by
    intro j hj
    induction j with
    | zero => simpa using hprod 0 hj
    | succ j ih =>
      have hh := hprod (j+1) hj
      have hi := ih (by omega)
      simp only [sub_mul,one_mul,mul_assoc,coeff_sub,coeff_C_mul,coeff_X_mul] at hh
      simp only [mul_assoc,coeff_sub,coeff_C_mul] at hi ⊢
      simp only [hi,mul_zero,sub_zero] at hh
      exact hh
  have hh := hz n hn
  simp only [coeff_sub] at hh
  change (jacLipschitzPolynomial M*jacPolynomial N).coeff n-
    (derivative (jacPolynomial N)).coeff n=0
  change (derivative (jacPolynomial N)).coeff n-
    (jacLipschitzPolynomial M*jacPolynomial N).coeff n=0 at hh
  linarith

theorem jacForcing_recurrence (M N n : ℕ) (hNM : N≤M) (hn : n<N) :
    (jacLipschitzPolynomial M*jacPolynomial N).coeff n=
      (n+1:ℝ)*(jacPolynomial N).coeff (n+1) := by
  have h := jacResidual_low M N n hNM hn
  simpa only [jacResidual,coeff_sub,coeff_derivative,sub_eq_zero,mul_comm] using h

theorem jacResidual_nonneg (M N n : ℕ) (hNM : N≤M) : 0≤(jacResidual M N).coeff n := by
  by_cases hn : n<N
  · rw [jacResidual_low M N n hNM hn]
  · have hd : (derivative (jacPolynomial N)).coeff n=0 := by
      rw [coeff_derivative,jacPolynomial_coeff,if_neg (by omega),zero_mul]
    simp only [jacResidual,coeff_sub,hd,sub_zero]
    exact coeff_mul_nonneg_all (jacLipschitzPolynomial_nonneg M) (jacPolynomial_nonneg N) n

end
end SolitonClassification.Rotating.UniversalMajorant

#print axioms SolitonClassification.Rotating.UniversalMajorant.jacForcing_recurrence
open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext,`Classical.choice,`Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (←collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked+1
  logInfo m!"Universal variation scalar audit passed: {checked} declarations; standard axioms only."
