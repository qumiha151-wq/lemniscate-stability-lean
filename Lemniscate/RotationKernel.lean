import Lemniscate.Algebra
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add

/-! The actual differential expression annihilates the rotational mode q*q'.
The hypotheses are the profile ODE and its first integral. Existence, period,
and identification with the geometric Bernoulli lemniscate remain separate.
-/
namespace Lemniscate

noncomputable def normalLinearization (q f : ℝ → ℝ) (x : ℝ) : ℝ :=
  -4*deriv (deriv (deriv (deriv f))) x
  -45*(q x)^2*deriv (deriv f) x
  -75*q x*deriv q x*deriv f x
  -((69/2:ℝ)+(45/2:ℝ)*(q x)^4)*f x

theorem rotation_kernel (q p : ℝ → ℝ)
    (hq : ∀ x, HasDerivAt q (p x) x)
    (hp : ∀ x, HasDerivAt p (-(q x)^3) x)
    (henergy : ∀ x, 2*(p x)^2+(q x)^4 = 1) :
    ∀ x, normalLinearization q (fun y => q y*p y) x = 0 := by
  have d1 : deriv (fun y => q y*p y) = fun y => (p y)^2-(q y)^4 := by
    funext x
    convert ((hq x).mul (hp x)).deriv using 1 <;>
      (try simp only [Pi.mul_def, Pi.pow_apply]) <;> ring
  have d2 : deriv (fun y => (p y)^2-(q y)^4) = fun y => -6*(q y)^3*p y := by
    funext x
    convert (((hp x).pow 2).sub ((hq x).pow 4)).deriv using 1 <;>
      (try simp only [Pi.sub_def, Pi.pow_apply]) <;> ring
  have d3 : deriv (fun y => -6*(q y)^3*p y) =
      fun y => -18*(q y)^2*(p y)^2+6*(q y)^6 := by
    funext x
    convert ((((hq x).pow 3).const_mul (-6)).mul (hp x)).deriv using 1 <;>
      (try simp only [Pi.mul_def, Pi.pow_apply]) <;> ring
  have d4 : deriv (fun y => -18*(q y)^2*(p y)^2+6*(q y)^6) =
      fun y => -36*q y*(p y)^3+72*(q y)^5*p y := by
    funext x
    convert (((((hq x).pow 2).const_mul (-18)).mul ((hp x).pow 2)).add
      (((hq x).pow 6).const_mul 6)).deriv using 1 <;>
      (try simp only [Pi.add_def, Pi.mul_def, Pi.pow_apply]) <;> ring
  intro x
  simp only [normalLinearization, d1, d2, d3, d4, (hq x).deriv]
  have h : (69/2:ℝ)*q x*p x*(2*(p x)^2+(q x)^4-1) = 0 := by
    rw [henergy x]
    ring
  nlinarith [h]

end Lemniscate
