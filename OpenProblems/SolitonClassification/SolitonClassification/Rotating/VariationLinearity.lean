import SolitonClassification.Rotating.VariationTaylor
import SolitonClassification.Rotating.ResidualODE
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Genuine linearity in the initial variation. This supports operator
norm bounds from uniform arbitrary-vector estimates without a column-count
factor. Interval errors checked separately by columns still need row sums. -/
namespace SolitonClassification.Rotating
noncomputable section
open Polynomial Finset
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem realConvolution_add_right (x y z : ℕ → ℝ) (n : ℕ) :
    realConvolution x (fun j=>y j+z j) n=realConvolution x y n+realConvolution x z n := by
  simp [realConvolution,mul_add,sum_add_distrib]

theorem realConvolution_mul_right (x y : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    realConvolution x (fun j=>c*y j) n=c*realConvolution x y n := by
  unfold realConvolution
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  ring

theorem variationRHS_add (c : ℕ → State) (q : ℕ → ℝ) (u v : ℕ → State) (n : ℕ) :
    variationRHS c q (fun j=>u j+v j) n=variationRHS c q u n+variationRHS c q v n := by
  ext i
  fin_cases i <;> simp [variationRHS,realConvolution_add_right] <;> ring

theorem variationRHS_smul (c : ℕ → State) (q : ℕ → ℝ) (u : ℕ → State) (r : ℝ) (n : ℕ) :
    variationRHS c q (fun j=>r • u j) n=r • variationRHS c q u n := by
  ext i
  fin_cases i <;> simp [variationRHS,Pi.smul_apply,smul_eq_mul,realConvolution_mul_right] <;> ring

theorem variationCoeff_add (a v w : State) (n : ℕ) :
    variationCoeff a (v+w) n=variationCoeff a v n+variationCoeff a w n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [variationCoeff_zero]
    | succ n =>
      apply smul_right_injective State (show (n+1:ℝ)≠0 by positivity)
      dsimp only
      rw [variationCoeff_recurrence,smul_add,variationCoeff_recurrence,variationCoeff_recurrence]
      rw [variationRHS_congr (taylorCoeff a) (taylorCoeff a)
        (squareCoeff (taylorCoeff a)) (squareCoeff (taylorCoeff a))
        (variationCoeff a (v+w)) (fun j=>variationCoeff a v j+variationCoeff a w j) n
        (by intros;rfl) (by intros;rfl) (fun j hj=>ih j (by omega))]
      exact variationRHS_add _ _ _ _ n

theorem variationCoeff_smul (a v : State) (r : ℝ) (n : ℕ) :
    variationCoeff a (r • v) n=r • variationCoeff a v n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [variationCoeff_zero]
    | succ n =>
      apply smul_right_injective State (show (n+1:ℝ)≠0 by positivity)
      dsimp only
      rw [variationCoeff_recurrence,smul_comm (n+1:ℝ) r,variationCoeff_recurrence]
      rw [variationRHS_congr (taylorCoeff a) (taylorCoeff a)
        (squareCoeff (taylorCoeff a)) (squareCoeff (taylorCoeff a))
        (variationCoeff a (r • v)) (fun j=>r • variationCoeff a v j) n
        (by intros;rfl) (by intros;rfl) (fun j hj=>ih j (by omega))]
      exact variationRHS_smul _ _ _ r n

def variationCoefficientLinearMap (a : State) (n : ℕ) : State →ₗ[ℝ] State where
  toFun := fun v=>variationCoeff a v n
  map_add' := fun v w=>variationCoeff_add a v w n
  map_smul' := fun r v=>variationCoeff_smul a v r n

def variationCoefficientMap (a : State) (n : ℕ) : State →L[ℝ] State :=
  (variationCoefficientLinearMap a n).toContinuousLinearMap

theorem variationCoefficientMap_apply (a v : State) (n : ℕ) :
    variationCoefficientMap a n v=variationCoeff a v n := rfl

def variationPolynomialMap (a : State) (N : ℕ) (t : ℝ) : State →L[ℝ] State :=
  ∑n∈range (N+1),(t^n) • variationCoefficientMap a n

theorem variationPolynomialMap_apply (a v : State) (N : ℕ) (t : ℝ) :
    variationPolynomialMap a N t v=polynomialPath (variationPolynomial a v N) t := by
  ext i
  simp [variationPolynomialMap,variationPolynomial,polynomialPath,variationCoefficientMap_apply,
    eval_finsetSum,Finset.sum_apply,smul_eq_mul,mul_comm]

def variationVelocityMap (a : State) (N : ℕ) (t : ℝ) : State →L[ℝ] State :=
  ∑n∈range (N+1),((n:ℝ)*t^(n-1)) • variationCoefficientMap a n

theorem variationPolynomialMap_hasDerivAt (a : State) (N : ℕ) (t : ℝ) :
    HasDerivAt (variationPolynomialMap a N) (variationVelocityMap a N t) t := by
  unfold variationPolynomialMap variationVelocityMap
  apply HasDerivAt.fun_sum
  intro n hn
  simpa using ((hasDerivAt_id t).pow n).smul_const (variationCoefficientMap a n)

theorem variationVelocityMap_apply (a v : State) (N : ℕ) (t : ℝ) :
    variationVelocityMap a N t v=polynomialVelocity (variationPolynomial a v N) t := by
  have hd := (variationPolynomialMap_hasDerivAt a N t).clm_apply (hasDerivAt_const t v)
  have he : (fun s=>variationPolynomialMap a N s v)=polynomialPath (variationPolynomial a v N) := by
    funext s
    exact variationPolynomialMap_apply a v N s
  rw [he] at hd
  simpa using hd.unique (polynomialPath_hasDerivAt _ t)

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.variationPolynomialMap_apply
#print axioms SolitonClassification.Rotating.variationVelocityMap_apply
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Actual variational-polynomial linearity audit passed for {count} declarations."
