import Lemniscate.ShortCircleForms
import Lemniscate.Bernstein

/-! The exact quartic conversion for the full periodic form. -/
namespace Lemniscate
open Complex Finset

theorem short_quartic_bernstein (c : Fin 5 → ℂ) (α : ℝ) :
    (∑ k : Fin 5, (α:ℂ)^k.val*c k) =
      ∑ j : Fin 5, (bernsteinBasis 4 j.val α:ℂ)*
        (∑ k : Fin 5, (shortBernsteinWeight j k:ℂ)*c k) := by
  norm_num [shortBernsteinWeight,bernsteinBasis,bernsteinPolynomial,
    Fin.sum_univ_succ,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_sub,Polynomial.eval_natCast,Nat.choose]
  push_cast
  ring

variable (T : ℝ) [Fact (0<T)]

theorem circle_reduced_shifted_bernstein
    (H : Fin 5 → circleH4Domain T → circleH4Domain T → ℂ)
    (α : ℝ) (f g : circleH4Domain T) :
    circleReducedBlochForm T H α f g+(1/2:ℂ)*inner ℂ (f:CircleL2 T) (g:CircleL2 T) =
      ∑ j : Fin 5, (bernsteinBasis 4 j.val α:ℂ)*circleShiftedBernsteinPairing T H j f g := by
  rw [circle_reduced_shifted_polynomial]
  exact short_quartic_bernstein (fun k => circleReducedShiftedCoefficient T H k f g) α

/-- Nonpositivity of the five full control forms implies the exact
half-unit L2 coercivity for every Bloch parameter in the half interval. -/
theorem circle_reduced_bound_of_bernstein
    (H : Fin 5 → circleH4Domain T → circleH4Domain T → ℂ)
    (f : circleH4Domain T)
    (hB : ∀ j : Fin 5, (circleShiftedBernsteinPairing T H j f f).re ≤ 0)
    (α : ℝ) (hα : 0≤α) (hα' : α≤1/2) :
    (circleReducedBlochForm T H α f f).re ≤ -(1/2:ℝ)*‖(f:CircleL2 T)‖^2 := by
  have he := congrArg Complex.re (circle_reduced_shifted_bernstein T H α f f)
  simp only [Complex.add_re, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at he
  have hs : (∑ j : Fin 5, bernsteinBasis 4 j.val α*
      (circleShiftedBernsteinPairing T H j f f).re) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    exact mul_nonpos_of_nonneg_of_nonpos (bernsteinBasis_nonneg 4 j.val α hα hα') (hB j)
  norm_num [inner_self_eq_norm_sq_to_K,pow_two] at he
  nlinarith

end Lemniscate
