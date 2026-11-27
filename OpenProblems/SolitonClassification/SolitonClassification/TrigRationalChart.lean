import SolitonClassification.ScalarReconstructionNecessity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Polynomial.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial Set Filter
open scoped Polynomial ContDiff
namespace ClosedSimilarity.TrigCurvature
def Q : ℝ[X] := X^2+1
def chart (u w t : ℝ) := u+(2/w)*Real.arctan t
def Represents (u w : ℝ) (f : ℝ → ℝ) (n : ℕ) (p : ℝ[X]) : Prop :=
  ∀ x, f (chart u w x)*(1+x^2)^n=p.eval x

theorem eval_Q (x : ℝ) : Q.eval x=1+x^2 := by simp [Q,add_comm]

theorem Q_prime : Prime Q := by
  apply Irreducible.prime
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hh : Q.natDegree=2 := by
      unfold Q
      compute_degree
      norm_num
    simp [hh]
  · intro x hx
    change Q.eval x=0 at hx
    rw [eval_Q] at hx
    nlinarith [sq_nonneg x]

theorem chart_hasDerivAt (u w x : ℝ) :
    HasDerivAt (chart u w) ((2/w)/(1+x^2)) x := by
  convert (((Real.hasDerivAt_arctan x).const_mul (2/w)).const_add u) using 1 <;>
    first | rfl | ring

theorem represents_deriv {u w : ℝ} (hw : w≠0) {f : ℝ → ℝ} (diff : Differentiable ℝ f)
    {n : ℕ} {p : ℝ[X]} (rep : Represents u w f n p) :
    Represents u w (deriv f) n (C (w/2)*(Q*p.derivative-C (n:ℝ)*Q.derivative*p)) := by
  intro x
  let y := 1+x^2
  have yn : y≠0 := ne_of_gt (by dsimp [y]; positivity)
  have dq : HasDerivAt (fun t : ℝ => 1+t^2) (Q.derivative.eval x) x := by
    simpa only [eval_Q] using Q.hasDerivAt x
  have dpow : HasDerivAt (fun t : ℝ => (1+t^2)^n)
      ((n:ℝ)*Q.derivative.eval x*y^n/y) x := by
    apply (dq.fun_pow n).congr_deriv
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.cast_succ,Nat.add_one_sub_one,pow_succ]
      change _ = (↑n+1) * Q.derivative.eval x * (y^n*y)/y
      field_simp [yn]
      ring
  have hf := ((diff (chart u w x)).hasDerivAt.comp x (chart_hasDerivAt u w x)).mul dpow
  have eq : (fun t => f (chart u w t)*(1+t^2)^n)=fun t => p.eval t := funext rep
  have hf' : HasDerivAt (fun t => p.eval t)
      (deriv f (chart u w x) * ((2/w)/y)*y^n+
        f (chart u w x)*((n:ℝ)*Q.derivative.eval x*y^n/y)) x := by
    rw [← eq]
    simpa only [Function.comp_def,smul_eq_mul,y] using! hf
  have hd := hf'.unique (p.hasDerivAt x)
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_sub,eval_Q]
  change deriv f (chart u w x)*y^n = w/2*(y*p.derivative.eval x-(n:ℝ)*Q.derivative.eval x*p.eval x)
  rw [←rep x]
  change deriv f (chart u w x)*y^n = w/2*(y*p.derivative.eval x-(n:ℝ)*Q.derivative.eval x*(f (chart u w x)*y^n))
  field_simp [yn,hw] at hd
  linear_combination hd / 2

end ClosedSimilarity.TrigCurvature
