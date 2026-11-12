import SolitonClassification.Rotating.TaylorCoefficients
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Gronwall

/-! The actual polynomial residual and a true-solution comparison.
Existence and tube confinement of the compared ODE solution are explicit
hypotheses here, not conclusions from the external numeric report. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Polynomial
open scoped ContDiff

theorem outerTube_convex : Convex ℝ outerTube := by
  intro x hx y hy a b ha hb hab
  change |(a • x+b • y) 0|≤17/2 ∧ |(a • x+b • y) 1|≤9/2 ∧
    |(a • x+b • y) 2|≤17/2 ∧ |(a • x+b • y) 3|≤17/2 ∧
    |(a • x+b • y) 4|≤1/50
  have h (i : Fin 6) (r : ℝ) (hx : |x i|≤r) (hy : |y i|≤r) :
      |(a • x+b • y) i|≤r := by
    change |a*x i+b*y i|≤r
    calc
      _ ≤ |a*x i|+|b*y i| := abs_add_le _ _
      _ = a*|x i|+b*|y i| := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
      _ ≤ a*r+b*r := add_le_add (mul_le_mul_of_nonneg_left hx ha)
        (mul_le_mul_of_nonneg_left hy hb)
      _ = r := by rw [←add_mul,hab,one_mul]
  exact ⟨h 0 _ hx.1 hy.1,h 1 _ hx.2.1 hy.2.1,h 2 _ hx.2.2.1 hy.2.2.1,
    h 3 _ hx.2.2.2.1 hy.2.2.2.1,h 4 _ hx.2.2.2.2 hy.2.2.2.2⟩

theorem field_lipschitz_on : LipschitzOnWith 17 field outerTube := by
  apply outerTube_convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜:=ℝ)
  · intro x hx
    exact field_smooth.differentiable (by simp) x
  · intro x hx
    exact field_fderiv_bound hx

def polynomialPath (P : StatePolynomial) (t : ℝ) : State := fun i => (P i).eval t
def polynomialVelocity (P : StatePolynomial) (t : ℝ) : State :=
  fun i => (derivative (P i)).eval t

theorem polynomialPath_hasDerivAt (P : StatePolynomial) (t : ℝ) :
    HasDerivAt (polynomialPath P) (polynomialVelocity P t) t := by
  apply hasDerivAt_pi.mpr
  intro i
  exact (P i).hasDerivAt t

theorem polynomial_residual_actual (a : State) (N : ℕ) (t : ℝ) :
    polynomialPath (taylorResidual a N) t=
      polynomialVelocity (taylorPolynomial a N) t-
        field (polynomialPath (taylorPolynomial a N) t) := by
  have h := polynomialField_eval (taylorPolynomial a N) t
  funext i
  have hi := congrFun h i
  change ((derivative (taylorPolynomial a N i))-
      polynomialField (taylorPolynomial a N) i).eval t=
      (derivative (taylorPolynomial a N i)).eval t-
        field (polynomialPath (taylorPolynomial a N) t) i
  rw [Polynomial.eval_sub,hi]
  rfl

/-- A proved bridge from a finite polynomial's residual to an actual ODE
solution on a segment. The solution's existence and confinement remain
separate obligations of a validated-step construction. -/
theorem polynomial_ode_comparison (a : State) (N : ℕ)
    {x : ℝ → State} {T ε δ : ℝ}
    (hx : ContinuousOn x (Icc 0 T))
    (hxd : ∀t∈Ico 0 T,HasDerivWithinAt x (field (x t)) (Ici t) t)
    (hxt : ∀t∈Ico 0 T,x t∈outerTube)
    (hpt : ∀t∈Ico 0 T,polynomialPath (taylorPolynomial a N) t∈outerTube)
    (hres : ∀t∈Ico 0 T,‖polynomialPath (taylorResidual a N) t‖≤ε)
    (hinit : dist (x 0) (polynomialPath (taylorPolynomial a N) 0)≤δ) :
    ∀t∈Icc 0 T,dist (x t) (polynomialPath (taylorPolynomial a N) t)≤
      gronwallBound δ 17 ε t := by
  have hp : Continuous (polynomialPath (taylorPolynomial a N)) := by
    exact continuous_iff_continuousAt.mpr fun t =>
      (polynomialPath_hasDerivAt _ t).continuousAt
  have hd := dist_le_of_approx_trajectories_ODE_of_mem
    (v:=fun _=>field) (s:=fun _=>outerTube) (K:=17) (εf:=0) (εg:=ε)
    (fun _ _=>field_lipschitz_on) hx hxd (by intros; simp) hxt hp.continuousOn
    (fun t _=>(polynomialPath_hasDerivAt _ t).hasDerivWithinAt) (by
      intro t ht
      simpa only [dist_eq_norm,←polynomial_residual_actual] using hres t ht) hpt hinit
  simpa only [zero_add,sub_zero,NNReal.coe_ofNat] using hd

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.polynomial_ode_comparison

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
  logInfo "Rotating polynomial-to-ODE comparison audit passed; standard axioms only."
