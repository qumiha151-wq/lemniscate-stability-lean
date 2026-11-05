import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! A smooth increasing parameter change with smooth inverse has a
strictly positive derivative, as required by oriented curve calculus. -/
namespace Lemniscate

/-- Differentiability of an increasing bijection and its inverse gives
strict positivity of its actual derivative. -/
theorem order_iso_deriv_pos (e : ℝ ≃o ℝ)
    (he : Differentiable ℝ (e : ℝ → ℝ))
    (hi : Differentiable ℝ (e.symm : ℝ → ℝ)) (x : ℝ) :
    0<deriv (e : ℝ → ℝ) x := by
  have hc := (hi (e x)).hasDerivAt.comp x (he x).hasDerivAt
  have hd : HasDerivAt (fun y : ℝ => y)
      (deriv (e.symm : ℝ → ℝ) (e x)*deriv (e : ℝ → ℝ) x) x := by
    simpa only [Function.comp_def,e.symm_apply_apply] using hc
  have hh := hd.unique (hasDerivAt_id x)
  have hn : deriv (e : ℝ → ℝ) x≠0 := by
    intro hzero
    rw [hzero,mul_zero] at hh
    exact zero_ne_one hh
  exact lt_of_le_of_ne e.monotone.deriv_nonneg hn.symm

end Lemniscate
