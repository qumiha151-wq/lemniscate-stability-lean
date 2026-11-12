import SolitonClassification.ScalarReconstructionResidual
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-! Intrinsic uniqueness of similarity parameters. For a nonconstant smooth
periodic curvature, the scalar equation determines both dilation and rotation.
This does not assert existence or classify its periodic solutions. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace ClosedSimilarity.ScalarReconstruction

theorem scalar_parameter_difference {k : ℝ → ℝ} {a₁ b₁ a₂ b₂ : ℝ}
    (h₁ : ScalarEquation k a₁ b₁) (h₂ : ScalarEquation k a₂ b₂) (s : ℝ) :
    (a₁-a₂)*k s^2+(b₁-b₂)*deriv k s=0 := by
  have h1 := h₁ s
  have h2 := h₂ s
  dsimp only [numerator,supportDerivative] at h1 h2
  linear_combination h2-h1

theorem periodic_square_integral_pos_at_nonzero {k : ℝ → ℝ} {L s₀ : ℝ}
    (hk : Continuous k) (hL : 0<L) (h₀ : k s₀≠0) :
    0 < ∫ s in s₀..s₀+L, k s^2 := by
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ : ℝ => (0:ℝ)) (g := fun s => k s^2)
    (show s₀<s₀+L by linarith) continuous_const.continuousOn (hk.pow 2).continuousOn
    (fun s _ => sq_nonneg _) ⟨s₀,⟨le_rfl,by linarith⟩,sq_pos_of_ne_zero h₀⟩
  simpa only [intervalIntegral.integral_zero] using h

/-- Dilation is uniquely determined by any nonzero smooth periodic scalar
curvature, including a nonzero constant curvature. -/
theorem dilation_unique_of_scalar_equations {k : ℝ → ℝ} {L a₁ b₁ a₂ b₂ : ℝ}
    (hk : ContDiff ℝ ∞ k) (hL : 0<L) (hp : Function.Periodic k L)
    (hnz : ∃s, k s≠0) (h₁ : ScalarEquation k a₁ b₁) (h₂ : ScalarEquation k a₂ b₂) :
    a₁=a₂ := by
  obtain ⟨s₀,h₀⟩ := hnz
  have hdk := (contDiff_infty_iff_deriv.mp hk).2
  have hi : (∫ s in s₀..s₀+L, deriv k s)=0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := s₀) (b := s₀+L) (fun s _ => (hk.differentiable (by simp) s).hasDerivAt)
      (hdk.continuous.intervalIntegrable s₀ (s₀+L))
    simpa only [hp s₀,sub_self] using h
  have hz : (∫ s in s₀..s₀+L, ((a₁-a₂)*k s^2+(b₁-b₂)*deriv k s))=0 := by
    calc
      _ = ∫ s in s₀..s₀+L, (0:ℝ) :=
        intervalIntegral.integral_congr (fun s _ => scalar_parameter_difference h₁ h₂ s)
      _ = 0 := intervalIntegral.integral_zero
  rw [intervalIntegral.integral_add
    (f := fun s => (a₁-a₂)*k s^2) (g := fun s => (b₁-b₂)*deriv k s)
    (((hk.continuous.pow 2).const_mul (a₁-a₂)).intervalIntegrable s₀ (s₀+L))
    ((hdk.continuous.const_mul (b₁-b₂)).intervalIntegrable s₀ (s₀+L)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    hi,mul_zero,add_zero] at hz
  have hpos := periodic_square_integral_pos_at_nonzero hk.continuous hL h₀
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (ne_of_gt hpos))

/-- Both parameters are intrinsic to a nonconstant periodic curvature.
Changing the support origin cannot give this curvature a different rotation
rate while retaining the actual scalar equation. -/
theorem scalar_parameters_unique_of_nonconstant {k : ℝ → ℝ} {L a₁ b₁ a₂ b₂ : ℝ}
    (hk : ContDiff ℝ ∞ k) (hL : 0<L) (hp : Function.Periodic k L)
    (hn : ∃s t, k s≠k t)
    (h₁ : ScalarEquation k a₁ b₁) (h₂ : ScalarEquation k a₂ b₂) :
    a₁=a₂ ∧ b₁=b₂ := by
  obtain ⟨s,t,hst⟩ := hn
  have hnz : ∃u, k u≠0 := by
    by_cases hs : k s=0
    · refine ⟨t,?_⟩
      intro ht
      exact hst (hs.trans ht.symm)
    · exact ⟨s,hs⟩
  have ha := dilation_unique_of_scalar_equations hk hL hp hnz h₁ h₂
  have hdnz : ∃u, deriv k u≠0 := by
    by_contra h
    push Not at h
    exact hst (is_const_of_deriv_eq_zero
      (fun u => hk.differentiable (by simp) u) h s t)
  obtain ⟨u,hu⟩ := hdnz
  have hd := scalar_parameter_difference h₁ h₂ u
  rw [ha,sub_self,zero_mul,zero_add] at hd
  exact ⟨ha,sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_right hu)⟩

end ClosedSimilarity.ScalarReconstruction

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`ClosedSimilarity).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains a do
          throwError "Scalar parameter uniqueness audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Scalar parameter uniqueness audit passed for {count} declarations; standard axioms only."
