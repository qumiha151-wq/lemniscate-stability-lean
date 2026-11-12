import SolitonClassification.Rotating.TaylorCoefficients

/-! Canonical full-state variational coefficients. No b row or theta column
is discarded. The polynomial operator is proved to evaluate to the actual
Frechet derivative of the six-dimensional field. -/
namespace SolitonClassification.Rotating
noncomputable section
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def variationRHS (c : ℕ → State) (q : ℕ → ℝ) (w : ℕ → State) (n : ℕ) : State :=
  ![8*w n 1,
    -3*(realConvolution q (fun j=>w j 0) n)/16-w n 2/8-
      (realConvolution (fun j=>c j 4) (fun j=>w j 3) n)/8-
      (realConvolution (fun j=>c j 3) (fun j=>w j 4) n)/8,
    -(realConvolution (fun j=>c j 0) (fun j=>w j 3) n)-
      (realConvolution (fun j=>c j 3) (fun j=>w j 0) n),
    realConvolution (fun j=>c j 0) (fun j=>w j 2) n+
      realConvolution (fun j=>c j 2) (fun j=>w j 0) n,
    0,w n 0]

lemma variationRHS_congr (c d : ℕ → State) (q r : ℕ → ℝ)
    (w z : ℕ → State) (n : ℕ)
    (hc : ∀j≤n,c j=d j) (hq : ∀j≤n,q j=r j) (hw : ∀j≤n,w j=z j) :
    variationRHS c q w n=variationRHS d r z n := by
  have hconv (i k : Fin 6) :
      realConvolution (fun j=>c j i) (fun j=>w j k) n=
      realConvolution (fun j=>d j i) (fun j=>z j k) n := by
    apply realConvolution_congr
    · intro j hj; rw [hc j hj]
    · intro j hj; rw [hw j hj]
  have hqconv : realConvolution q (fun j=>w j 0) n=
      realConvolution r (fun j=>z j 0) n := by
    apply realConvolution_congr _ _ _ _ _ hq
    intro j hj; rw [hw j hj]
  simp only [variationRHS,hconv,hqconv,hw n le_rfl]

def variationCoeff (a v : State) : ℕ → State
  | 0 => v
  | n+1 => (1/(n+1:ℝ)) • variationRHS (taylorCoeff a) (squareCoeff (taylorCoeff a))
      (fun j=>if _h : j≤n then variationCoeff a v j else 0) n
termination_by n=>n
decreasing_by omega

lemma variationCoeff_zero (a v : State) : variationCoeff a v 0=v := by rw [variationCoeff]

theorem variationCoeff_recurrence (a v : State) (n : ℕ) :
    (n+1:ℝ) • variationCoeff a v (n+1)=
      variationRHS (taylorCoeff a) (squareCoeff (taylorCoeff a)) (variationCoeff a v) n := by
  rw [variationCoeff]
  have he : variationRHS (taylorCoeff a) (squareCoeff (taylorCoeff a))
      (fun j=>if h : j≤n then variationCoeff a v j else 0) n=
      variationRHS (taylorCoeff a) (squareCoeff (taylorCoeff a)) (variationCoeff a v) n := by
    apply variationRHS_congr _ _ _ _ _ _ n (by intros; rfl) (by intros; rfl)
    intro j hj; simp [hj]
  rw [he,smul_smul]
  simp [show (n+1:ℝ)≠0 by positivity]

def polynomialVariation (P W : StatePolynomial) : StatePolynomial :=
  ![C 8*W 1,
    -C (3/16)*((P 0)^2*W 0)-C (1/8)*W 2-C (1/8)*(P 4*W 3)-C (1/8)*(P 3*W 4),
    -(P 0*W 3)-(P 3*W 0),P 0*W 2+P 2*W 0,0,W 0]

theorem polynomialVariation_eval (P W : StatePolynomial) (t : ℝ) :
    (fun i=>(polynomialVariation P W i).eval t)=
      fderiv ℝ field (fun i=>(P i).eval t) (fun i=>(W i).eval t) := by
  rw [field_fderiv_apply]
  funext i
  fin_cases i <;> simp [polynomialVariation,linear] <;> ring

lemma polynomialVariation_coeff (P W : StatePolynomial) (n : ℕ) :
    (fun i=>(polynomialVariation P W i).coeff n)=
      variationRHS (fun j i=>(P i).coeff j) (squareCoeff (fun j i=>(P i).coeff j))
        (fun j i=>(W i).coeff j) n := by
  funext i
  fin_cases i <;> dsimp only [polynomialVariation,variationRHS]
  all_goals simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',neg_mul,
    coeff_add,coeff_sub,coeff_neg,coeff_zero,coeff_C_mul]
  all_goals simp only [realConvolution,squareCoeff,pow_two,coeff_mul]
  all_goals ring

def variationPolynomial (a v : State) (N : ℕ) : StatePolynomial := fun i=>
  ∑n∈Finset.range (N+1),monomial n (variationCoeff a v n i)

lemma variationPolynomial_coeff (a v : State) (N n : ℕ) (i : Fin 6) :
    (variationPolynomial a v N i).coeff n=if n≤N then variationCoeff a v n i else 0 := by
  simp [variationPolynomial,coeff_monomial,Finset.mem_range]

def variationResidual (a v : State) (N : ℕ) : StatePolynomial := fun i=>
  derivative (variationPolynomial a v N i)-
    polynomialVariation (taylorPolynomial a N) (variationPolynomial a v N) i

theorem variationResidual_low_zero (a v : State) (N n : ℕ) (hn : n<N) (i : Fin 6) :
    (variationResidual a v N i).coeff n=0 := by
  have hc : ∀j≤n,(fun i=>(taylorPolynomial a N i).coeff j)=taylorCoeff a j := by
    intro j hj; funext i; rw [taylorPolynomial_coeff,if_pos (by omega)]
  have hq : ∀j≤n,squareCoeff (fun j i=>(taylorPolynomial a N i).coeff j) j=
      squareCoeff (taylorCoeff a) j := by
    intro j hj; apply squareCoeff_congr; intro k hk; exact hc k (by omega)
  have hw : ∀j≤n,(fun i=>(variationPolynomial a v N i).coeff j)=variationCoeff a v j := by
    intro j hj; funext i; rw [variationPolynomial_coeff,if_pos (by omega)]
  have hr := congrFun (variationCoeff_recurrence a v n) i
  have hp := congrFun (polynomialVariation_coeff (taylorPolynomial a N) (variationPolynomial a v N) n) i
  rw [variationRHS_congr _ _ _ _ _ _ n hc hq hw] at hp
  simp only [variationResidual,coeff_sub,coeff_derivative,hp]
  rw [variationPolynomial_coeff,if_pos (by omega)]
  simpa only [Pi.smul_apply,smul_eq_mul,mul_comm] using sub_eq_zero.mpr hr

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.variationResidual_low_zero
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Actual six-state variational polynomial audit passed."
