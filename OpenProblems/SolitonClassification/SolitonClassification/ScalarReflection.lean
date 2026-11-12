import SolitonClassification.ScalarParameterUniqueness
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Reflection of the actual scalar equation reverses the rotation parameter.
A nonconstant reflection-even curvature therefore cannot rotate. These are
necessary conditions; no periodic-solution existence is asserted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.ScalarReconstruction

theorem second_deriv_reflect (k : ℝ → ℝ) (c s : ℝ) :
    deriv (deriv (fun u => k (c-u))) s = deriv (deriv k) (c-s) := by
  have hd : deriv (fun u => k (c-u)) = fun u => -deriv k (c-u) :=
    funext (deriv_comp_const_sub k c)
  rw [hd]
  rw [deriv.fun_neg, deriv_comp_const_sub, neg_neg]

theorem force_reflect (k : ℝ → ℝ) (c : ℝ) :
    force (fun u => k (c-u)) = fun u => force k (c-u) := by
  funext s
  simp only [force, second_deriv_reflect]

/-- Reflecting the scalar argument keeps dilation and reverses rotation
in the actual degenerate fourth-order equation. This is a statement about
the function k(c-s), not the signed-curvature rule for reversing a curve's
orientation, which would also negate curvature. -/
theorem scalarEquation_reflect {k : ℝ → ℝ} {a b : ℝ}
    (hS : ScalarEquation k a b) (c : ℝ) :
    ScalarEquation (fun u => k (c-u)) a (-b) := by
  intro s
  have h := hS (c-s)
  dsimp only [numerator, supportDerivative] at h ⊢
  rw [force_reflect, second_deriv_reflect, deriv_comp_const_sub,
    deriv_comp_const_sub]
  linear_combination h

/-- Reflection-even nonconstant curvature forces zero rotation. A period
is not needed. The reflection is s ↦ c-s, with center c/2. -/
theorem rotation_zero_of_reflection {k : ℝ → ℝ} {a b c : ℝ}
    (hk : Differentiable ℝ k) (hn : ∃ s t, k s ≠ k t)
    (hS : ScalarEquation k a b) (hr : ∀ s, k (c-s)=k s) : b=0 := by
  have he : (fun s => k (c-s))=k := funext hr
  have hR : ScalarEquation k a (-b) := by
    simpa only [he] using scalarEquation_reflect hS c
  obtain ⟨s,t,hst⟩ := hn
  have hdnz : ∃ u, deriv k u ≠ 0 := by
    by_contra h
    push Not at h
    exact hst (is_const_of_deriv_eq_zero hk h s t)
  obtain ⟨u,hu⟩ := hdnz
  have h := scalar_parameter_difference hS hR u
  rw [sub_self,zero_mul,zero_add] at h
  have hb := (mul_eq_zero.mp h).resolve_right hu
  linarith

theorem no_reflection_of_nonzero_rotation {k : ℝ → ℝ} {a b : ℝ}
    (hk : Differentiable ℝ k) (hn : ∃ s t, k s ≠ k t)
    (hS : ScalarEquation k a b) (hb : b ≠ 0) :
    ¬ ∃ c, ∀ s, k (c-s)=k s := by
  rintro ⟨c,hc⟩
  exact hb (rotation_zero_of_reflection hk hn hS hc)

end ClosedSimilarity.ScalarReconstruction

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`ClosedSimilarity).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains a do
          throwError "Scalar reflection audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Scalar reflection audit passed for {count} declarations; standard axioms only."
