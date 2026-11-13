module

public import SolitonClassification.Rotating.AnalyticMajorantVector
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Eval.Degree

@[expose] public section

/-! The universal majorant bounds Rotating.taylorCoeff itself.
Polynomial-lift bookkeeping is independently adapted from this workspace's
CentroidEscape/VectorPolynomial.lean; there is no cross-problem import.
The bridge uses the already defined actual field recurrence, not a second
canonical sequence with an unproved identification. All orders are finite. -/
namespace SolitonClassification.Rotating.UniversalMajorant
noncomputable section
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def vectorPolynomialCoeff (P : StatePolynomial) (n : ℕ) : State := fun i => (P i).coeff n
def vectorPolynomialEval (P : StatePolynomial) (s : ℝ) : State := fun i => (P i).eval s

def polynomialLinear (a : State) (P : StatePolynomial) : StatePolynomial :=
  ![C 8*P 1,C (-3*(a 0)^2/16)*P 0-C (1/8)*P 2-C (a 4/8)*P 3-C (a 3/8)*P 4,
    C (-a 0)*P 3-C (a 3)*P 0,C (a 0)*P 2+C (a 2)*P 0,0,P 0]

def polynomialBilinear (a : State) (P Q : StatePolynomial) : StatePolynomial :=
  ![0,C (-3*a 0/16)*(P 0*Q 0)-C (1/8)*(P 4*Q 3),-(P 0*Q 3),P 0*Q 2,0,0]

def polynomialTrilinear (P Q R : StatePolynomial) : StatePolynomial :=
  ![0,C (-1/16)*(P 0*(Q 0*R 0)),0,0,0,0]

lemma polynomialLinear_eval (a : State) (P : StatePolynomial) (s : ℝ) :
    vectorPolynomialEval (polynomialLinear a P) s=linear a (vectorPolynomialEval P s) := by
  ext i
  fin_cases i <;> simp [vectorPolynomialEval,polynomialLinear,linear] <;> ring

lemma polynomialBilinear_eval (a : State) (P Q : StatePolynomial) (s : ℝ) :
    vectorPolynomialEval (polynomialBilinear a P Q) s=
      bilinear a (vectorPolynomialEval P s) (vectorPolynomialEval Q s) := by
  ext i
  fin_cases i <;> simp [vectorPolynomialEval,polynomialBilinear,bilinear]
  all_goals ring

lemma polynomialTrilinear_eval (P Q R : StatePolynomial) (s : ℝ) :
    vectorPolynomialEval (polynomialTrilinear P Q R) s=
      trilinear (vectorPolynomialEval P s) (vectorPolynomialEval Q s) (vectorPolynomialEval R s) := by
  ext i
  fin_cases i <;> simp [vectorPolynomialEval,polynomialTrilinear,trilinear]
  all_goals ring

lemma polynomialLinear_coeff (a : State) (P : StatePolynomial) (n : ℕ) :
    vectorPolynomialCoeff (polynomialLinear a P) n=linear a (vectorPolynomialCoeff P n) := by
  ext i
  fin_cases i <;> dsimp only [vectorPolynomialCoeff,polynomialLinear,linear]
  all_goals simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',coeff_C_mul,
    coeff_add,coeff_sub,coeff_zero]
  all_goals ring

lemma polynomialBilinear_coeff (a : State) (P Q : StatePolynomial) (n : ℕ) :
    vectorPolynomialCoeff (polynomialBilinear a P Q) n=
      ∑ ij ∈ Finset.antidiagonal n, bilinear a (vectorPolynomialCoeff P ij.1)
        (vectorPolynomialCoeff Q ij.2) := by
  ext i
  fin_cases i <;> simp only [Finset.sum_apply] <;>
    dsimp only [vectorPolynomialCoeff,polynomialBilinear,bilinear]
  all_goals simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',coeff_C_mul,
    coeff_sub,coeff_zero,coeff_neg]
  all_goals simp only [coeff_mul,Finset.sum_sub_distrib,
    Finset.mul_sum,Finset.sum_const_zero,mul_assoc]
  all_goals ring_nf
  all_goals simp only [Finset.sum_neg_distrib]

lemma polynomialTrilinear_coeff (P Q R : StatePolynomial) (n : ℕ) :
    vectorPolynomialCoeff (polynomialTrilinear P Q R) n=
      ∑ ij ∈ Finset.antidiagonal n, ∑ jk ∈ Finset.antidiagonal ij.2,
        trilinear (vectorPolynomialCoeff P ij.1) (vectorPolynomialCoeff Q jk.1)
          (vectorPolynomialCoeff R jk.2) := by
  ext i
  fin_cases i <;> simp only [Finset.sum_apply] <;>
    dsimp only [vectorPolynomialCoeff,polynomialTrilinear,trilinear]
  all_goals simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',coeff_C_mul,coeff_zero]
  all_goals simp only [coeff_mul,Finset.mul_sum,Finset.sum_const_zero,mul_assoc]
  all_goals ring_nf

def constantVectorPolynomial (a : State) : StatePolynomial := fun i => C (a i)

def displacedPolynomialField (a : State) (P : StatePolynomial) : StatePolynomial :=
  constantVectorPolynomial (field a)+polynomialLinear a P+
    polynomialBilinear a P P+polynomialTrilinear P P P

lemma vectorPolynomialCoeff_add (P Q : StatePolynomial) (n : ℕ) :
    vectorPolynomialCoeff (P+Q) n=vectorPolynomialCoeff P n+vectorPolynomialCoeff Q n := by
  ext i
  simp [vectorPolynomialCoeff]

lemma vectorPolynomialEval_add (P Q : StatePolynomial) (s : ℝ) :
    vectorPolynomialEval (P+Q) s=vectorPolynomialEval P s+vectorPolynomialEval Q s := by
  ext i
  simp [vectorPolynomialEval]

lemma constantVectorPolynomial_coeff (a : State) (n : ℕ) :
    vectorPolynomialCoeff (constantVectorPolynomial a) n=if n=0 then a else 0 := by
  ext i
  by_cases h : n=0 <;> simp [vectorPolynomialCoeff,constantVectorPolynomial,coeff_C,h]

lemma constantVectorPolynomial_eval (a : State) (s : ℝ) :
    vectorPolynomialEval (constantVectorPolynomial a) s=a := by
  ext i
  simp [vectorPolynomialEval,constantVectorPolynomial]

lemma displacedPolynomialField_coeff (a : State) (P : StatePolynomial) (n : ℕ) :
    vectorPolynomialCoeff (displacedPolynomialField a P) n=
      vectorTaylorRHS a (vectorPolynomialCoeff P) n := by
  simp only [displacedPolynomialField,vectorPolynomialCoeff_add,constantVectorPolynomial_coeff,
    polynomialLinear_coeff,polynomialBilinear_coeff,polynomialTrilinear_coeff,
    vectorTaylorRHS,quadraticTaylorCoeff,cubicTaylorCoeff]

lemma displacedPolynomialField_eval (a : State) (P : StatePolynomial) (s : ℝ) :
    vectorPolynomialEval (displacedPolynomialField a P) s=field (a+vectorPolynomialEval P s) := by
  simp only [displacedPolynomialField,vectorPolynomialEval_add,constantVectorPolynomial_eval,
    polynomialLinear_eval,polynomialBilinear_eval,polynomialTrilinear_eval,field_expansion]

/-- This polynomial lift is the existing actual polynomialField after a shift. -/
lemma displacedPolynomialField_eq (a : State) (P : StatePolynomial) :
    displacedPolynomialField a P=polynomialField (fun i => C (a i)+P i) := by
  funext i
  apply Polynomial.funext
  intro t
  have h1 := congrFun (displacedPolynomialField_eval a P t) i
  have h2 := congrFun (polynomialField_eval (fun i => C (a i)+P i) t) i
  simp only [eval_add,eval_C] at h2
  exact h1.trans h2.symm

/-- Remove only the constant a from the PRE-EXISTING actual coefficient sequence. -/
def actualDisplacementCoeff (a : State) (n : ℕ) : State :=
  if n=0 then 0 else taylorCoeff a n

lemma actualDisplacementCoeff_zero (a : State) : actualDisplacementCoeff a 0=0 := by
  simp [actualDisplacementCoeff]

lemma actualDisplacementCoeff_succ (a : State) (n : ℕ) :
    actualDisplacementCoeff a (n+1)=taylorCoeff a (n+1) := by
  simp [actualDisplacementCoeff]

def actualDisplacementPolynomial (a : State) (N : ℕ) : StatePolynomial :=
  fun i => taylorPolynomial a N i-C (a i)

lemma actualDisplacementPolynomial_coeff (a : State) (N n : ℕ) :
    vectorPolynomialCoeff (actualDisplacementPolynomial a N) n=
      if n≤N then actualDisplacementCoeff a n else 0 := by
  ext i
  by_cases hn : n≤N
  · by_cases hz : n=0
    · subst n
      simp [vectorPolynomialCoeff,actualDisplacementPolynomial,taylorPolynomial_coeff,
        actualDisplacementCoeff,taylorCoeff_zero]
    · simp [vectorPolynomialCoeff,actualDisplacementPolynomial,taylorPolynomial_coeff,
        actualDisplacementCoeff,hn,hz,coeff_C]
  · have hz : n≠0 := by omega
    simp [vectorPolynomialCoeff,actualDisplacementPolynomial,taylorPolynomial_coeff,hn,hz,coeff_C]

/-- The original Taylor recurrence, with its nonzero constant a, equals the
zero-constant displacement recurrence after the proved polynomial expansion. -/
theorem actualDisplacementCoeff_recurrence (a : State) (n : ℕ) :
    (n+1:ℝ) • actualDisplacementCoeff a (n+1)=
      vectorTaylorRHS a (actualDisplacementCoeff a) n := by
  have hc : ∀ j≤n, vectorPolynomialCoeff (taylorPolynomial a n) j=taylorCoeff a j := by
    intro j hj
    funext i
    exact (taylorPolynomial_coeff a n j i).trans (if_pos hj)
  have hs : ∀ j≤n, squareCoeff (vectorPolynomialCoeff (taylorPolynomial a n)) j=
      squareCoeff (taylorCoeff a) j := by
    intro j hj
    apply squareCoeff_congr
    intro k hk
    exact hc k (by omega)
  have hactual := polynomialField_coeff (taylorPolynomial a n) n
  change vectorPolynomialCoeff (polynomialField (taylorPolynomial a n)) n=
    realTaylorRHS (vectorPolynomialCoeff (taylorPolynomial a n))
      (squareCoeff (vectorPolynomialCoeff (taylorPolynomial a n))) n at hactual
  rw [realTaylorRHS_congr _ _ _ _ n hc hs] at hactual
  have hd : ∀ j≤n, vectorPolynomialCoeff (actualDisplacementPolynomial a n) j=
      actualDisplacementCoeff a j := by
    intro j hj
    rw [actualDisplacementPolynomial_coeff,if_pos hj]
  have hshift : (fun i => C (a i)+actualDisplacementPolynomial a n i)=taylorPolynomial a n := by
    funext i
    simp [actualDisplacementPolynomial]
  have hp := displacedPolynomialField_coeff a (actualDisplacementPolynomial a n) n
  rw [displacedPolynomialField_eq,hshift,vectorTaylorRHS_congr a _ _ n hd] at hp
  rw [actualDisplacementCoeff_succ,taylorCoeff_recurrence]
  exact hactual.symm.trans hp

/-- Main conclusion: the existing actual coefficients obey the universal
majorant at every finite order. No coefficient or recurrence assumption. -/
theorem actualDisplacementCoeff_majorized {a : State} (ha : a∈innerTube) (N : ℕ) :
    ∀ n≤N, ‖actualDisplacementCoeff a n‖≤(displacementPolynomial N).coeff n :=
  vectorTaylor_majorized ha N _ (actualDisplacementCoeff_zero a)
    (fun n _ => actualDisplacementCoeff_recurrence a n)

theorem taylorCoeff_majorized {a : State} (ha : a∈innerTube) (N n : ℕ)
    (hn : 0<n) (hN : n≤N) : ‖taylorCoeff a n‖≤(displacementPolynomial N).coeff n := by
  simpa only [actualDisplacementCoeff,if_neg (Nat.ne_of_gt hn)] using
    actualDisplacementCoeff_majorized ha N n hN

theorem actualDisplacementPolynomial_coeff_majorized {a : State} (ha : a∈innerTube)
    (N n : ℕ) : ‖vectorPolynomialCoeff (actualDisplacementPolynomial a N) n‖≤
      (displacementPolynomial N).coeff n := by
  rw [actualDisplacementPolynomial_coeff]
  split_ifs with hn
  · exact actualDisplacementCoeff_majorized ha N n hn
  · simpa only [norm_zero] using displacementPolynomial_nonneg N n

/-- Any finite vector polynomial is bounded for either time direction by
any scalar coefficient majorant. Nonnegative scalar coefficients follow
already from the assumed norm bounds; no extra positivity hypothesis. -/
theorem vectorPolynomialEval_norm_le (P : StatePolynomial) (q : ℝ[X])
    (hq : ∀ n, ‖vectorPolynomialCoeff P n‖≤q.coeff n) (t : ℝ) :
    ‖vectorPolynomialEval P t‖≤q.eval |t| := by
  let M := max (Finset.univ.sup fun i : Fin 6 => (P i).natDegree) q.natDegree+1
  have hP (i : Fin 6) : (P i).natDegree<M := by
    have hi : (P i).natDegree≤Finset.univ.sup (fun i : Fin 6 => (P i).natDegree) :=
      Finset.le_sup (s:=Finset.univ) (f:=fun i : Fin 6 => (P i).natDegree) (Finset.mem_univ i)
    exact Nat.lt_succ_of_le (hi.trans (le_max_left _ _))
  have hQ : q.natDegree<M := Nat.lt_succ_of_le (le_max_right _ _)
  have he : vectorPolynomialEval P t=
      ∑ n ∈ Finset.range M, t^n • vectorPolynomialCoeff P n := by
    ext i
    simp only [vectorPolynomialEval,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      vectorPolynomialCoeff]
    rw [Polynomial.eval_eq_sum_range' (hP i)]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [he,Polynomial.eval_eq_sum_range' hQ]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_smul,Real.norm_eq_abs,abs_pow]
  exact (mul_le_mul_of_nonneg_left (hq n) (pow_nonneg (abs_nonneg t) n)).trans_eq (mul_comm _ _)

lemma actualDisplacementPolynomial_eval (a : State) (N : ℕ) (t : ℝ) :
    vectorPolynomialEval (actualDisplacementPolynomial a N) t=
      (fun i => (taylorPolynomial a N i).eval t)-a := by
  ext i
  simp [vectorPolynomialEval,actualDisplacementPolynomial]

/-- Two-sided excursion of the PRE-EXISTING actual Taylor polynomial. -/
theorem taylorPolynomial_excursion {a : State} (ha : a∈innerTube) (N : ℕ) (t : ℝ) :
    ‖(fun i => (taylorPolynomial a N i).eval t)-a‖≤(displacementPolynomial N).eval |t| := by
  rw [←actualDisplacementPolynomial_eval]
  exact vectorPolynomialEval_norm_le _ _ (actualDisplacementPolynomial_coeff_majorized ha N) t

end
end SolitonClassification.Rotating.UniversalMajorant

#print axioms SolitonClassification.Rotating.UniversalMajorant.actualDisplacementCoeff_recurrence
#print axioms SolitonClassification.Rotating.UniversalMajorant.taylorCoeff_majorized
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
  logInfo m!"Universal actual-Taylor bridge audit passed: {checked} declarations; standard axioms only."

end
