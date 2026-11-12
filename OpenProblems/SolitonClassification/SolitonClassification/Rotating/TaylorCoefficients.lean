import SolitonClassification.Rotating.Field
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.List.NatAntidiagonal

/-! Canonical coefficients of the actual six-dimensional field.
The finite polynomial residual vanishes through the requested order.
This algebraic statement does not assert an infinite-series convergence or
an ODE truncation-error bound; those are separate analytic obligations. -/
namespace SolitonClassification.Rotating
noncomputable section
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def realConvolution (x y : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ ij ∈ Finset.antidiagonal n, x ij.1*y ij.2

def squareCoeff (c : ℕ → State) (n : ℕ) : ℝ :=
  realConvolution (fun j => c j 0) (fun j => c j 0) n

def realTaylorRHS (c : ℕ → State) (q : ℕ → ℝ) (n : ℕ) : State :=
  ![8*c n 1,
    -(realConvolution q (fun j => c j 0) n)/16-c n 2/8-
      (realConvolution (fun j => c j 4) (fun j => c j 3) n)/8,
    -(realConvolution (fun j => c j 0) (fun j => c j 3) n),
    (if n=0 then 1 else 0)+realConvolution (fun j => c j 0) (fun j => c j 2) n,
    0,c n 0]

lemma realConvolution_congr (x y x' y' : ℕ → ℝ) (n : ℕ)
    (hx : ∀j≤n,x j=x' j) (hy : ∀j≤n,y j=y' j) :
    realConvolution x y n=realConvolution x' y' n := by
  apply Finset.sum_congr rfl
  intro ij hij
  have h := Finset.mem_antidiagonal.mp hij
  rw [hx ij.1 (by omega),hy ij.2 (by omega)]

lemma squareCoeff_congr (c d : ℕ → State) (n : ℕ)
    (h : ∀j≤n,c j=d j) : squareCoeff c n=squareCoeff d n := by
  apply realConvolution_congr
  all_goals intro j hj; rw [h j hj]

lemma realTaylorRHS_congr (c d : ℕ → State) (q r : ℕ → ℝ) (n : ℕ)
    (hc : ∀j≤n,c j=d j) (hq : ∀j≤n,q j=r j) :
    realTaylorRHS c q n=realTaylorRHS d r n := by
  have hconv (i k : Fin 6) :
      realConvolution (fun j => c j i) (fun j => c j k) n=
      realConvolution (fun j => d j i) (fun j => d j k) n := by
    apply realConvolution_congr
    all_goals intro j hj; rw [hc j hj]
  have hcube : realConvolution q (fun j => c j 0) n=
      realConvolution r (fun j => d j 0) n := by
    apply realConvolution_congr _ _ _ _ _ hq
    intro j hj; rw [hc j hj]
  simp only [realTaylorRHS,hconv,hcube,hc n le_rfl]

def taylorCoeff (a : State) : ℕ → State
  | 0 => a
  | n+1 => (1/(n+1:ℝ)) • realTaylorRHS
      (fun j => if _h : j≤n then taylorCoeff a j else 0)
      (squareCoeff (fun j => if _h : j≤n then taylorCoeff a j else 0)) n
termination_by n => n
decreasing_by all_goals omega

lemma taylorCoeff_zero (a : State) : taylorCoeff a 0=a := by rw [taylorCoeff]

theorem taylorCoeff_recurrence (a : State) (n : ℕ) :
    (n+1:ℝ) • taylorCoeff a (n+1)=
      realTaylorRHS (taylorCoeff a) (squareCoeff (taylorCoeff a)) n := by
  rw [taylorCoeff]
  have he : realTaylorRHS
      (fun j => if h : j≤n then taylorCoeff a j else 0)
      (squareCoeff (fun j => if h : j≤n then taylorCoeff a j else 0)) n=
      realTaylorRHS (taylorCoeff a) (squareCoeff (taylorCoeff a)) n := by
    apply realTaylorRHS_congr
    · intro j hj; simp [hj]
    · intro j hj
      apply squareCoeff_congr
      intro k hk
      simp [show k≤n by omega]
  rw [he,smul_smul]
  simp [show (n+1:ℝ)≠0 by positivity]

abbrev StatePolynomial := Fin 6 → ℝ[X]

def polynomialField (P : StatePolynomial) : StatePolynomial :=
  ![C 8*P 1,-C (1/16)*((P 0)^2*P 0)-C (1/8)*P 2-C (1/8)*(P 4*P 3),
    -(P 0*P 3),1+P 0*P 2,0,P 0]

theorem polynomialField_eval (P : StatePolynomial) (t : ℝ) :
    (fun i => (polynomialField P i).eval t)=field (fun i => (P i).eval t) := by
  funext i
  fin_cases i <;> simp [polynomialField,field] <;> ring

lemma polynomialField_coeff (P : StatePolynomial) (n : ℕ) :
    (fun i => (polynomialField P i).coeff n)=
      realTaylorRHS (fun j i => (P i).coeff j)
        (squareCoeff (fun j i => (P i).coeff j)) n := by
  funext i
  fin_cases i <;> dsimp only [polynomialField,realTaylorRHS]
  all_goals simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',neg_mul,
    coeff_add,coeff_sub,coeff_neg,coeff_zero,coeff_one,coeff_C_mul]
  all_goals simp only [realConvolution,squareCoeff,pow_two,coeff_mul]
  all_goals ring

def taylorPolynomial (a : State) (N : ℕ) : StatePolynomial := fun i =>
  ∑ n ∈ Finset.range (N+1),monomial n (taylorCoeff a n i)

lemma taylorPolynomial_coeff (a : State) (N n : ℕ) (i : Fin 6) :
    (taylorPolynomial a N i).coeff n=if n≤N then taylorCoeff a n i else 0 := by
  simp [taylorPolynomial,coeff_monomial,Finset.mem_range,Nat.lt_succ_iff]

def taylorResidual (a : State) (N : ℕ) : StatePolynomial := fun i =>
  derivative (taylorPolynomial a N i)-polynomialField (taylorPolynomial a N) i

theorem taylorResidual_low_zero (a : State) (N n : ℕ) (hn : n<N) (i : Fin 6) :
    (taylorResidual a N i).coeff n=0 := by
  have hc : ∀j≤n,(fun i => (taylorPolynomial a N i).coeff j)=taylorCoeff a j := by
    intro j hj; funext i
    rw [taylorPolynomial_coeff,if_pos (by omega)]
  have hs : ∀j≤n,squareCoeff (fun j i => (taylorPolynomial a N i).coeff j) j=
      squareCoeff (taylorCoeff a) j := by
    intro j hj
    apply squareCoeff_congr
    intro k hk; exact hc k (by omega)
  have hr := congrFun (taylorCoeff_recurrence a n) i
  have hp := congrFun (polynomialField_coeff (taylorPolynomial a N) n) i
  rw [realTaylorRHS_congr _ _ _ _ n hc hs] at hp
  simp only [taylorResidual,coeff_sub,coeff_derivative,hp]
  rw [taylorPolynomial_coeff,if_pos (by omega)]
  simpa only [Pi.smul_apply,smul_eq_mul,mul_comm] using sub_eq_zero.mpr hr

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.taylorResidual_low_zero

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
  logInfo "Rotating canonical Taylor/residual audit passed; standard axioms only."
