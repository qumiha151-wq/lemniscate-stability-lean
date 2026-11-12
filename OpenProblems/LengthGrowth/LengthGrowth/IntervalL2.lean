import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Elementary interval Cauchy--Schwarz, with no `Lp` representation
or coercivity assumptions. This auxiliary module is independent of
all other open-problem projects. -/

noncomputable section
open MeasureTheory
namespace LengthGrowth

theorem interval_integral_mul_sq_le {f g : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hab : a ≤ b) :
    (∫ s in a..b, f s * g s)^2 ≤
      (∫ s in a..b, f s ^ 2) * (∫ s in a..b, g s ^ 2) := by
  let A := ∫ s in a..b, f s ^ 2
  let B := ∫ s in a..b, f s * g s
  let C := ∫ s in a..b, g s ^ 2
  have hpoly : ∀ t : ℝ, 0 ≤ C * (t*t) + (2*B)*t + A := by
    intro t
    have hpos : 0 ≤ ∫ s in a..b, (f s + t * g s)^2 :=
      intervalIntegral.integral_nonneg_of_forall hab (fun s => sq_nonneg _)
    have heq : (fun s => (f s + t*g s)^2) =
        (fun s => f s^2 + (2*t)*(f s*g s) + (t*t)*(g s^2)) := by
      funext s
      ring
    rw [heq, intervalIntegral.integral_add,
      intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hpos
    · dsimp [A, B, C]
      nlinarith
    · exact (hf.pow 2).intervalIntegrable _ _
    · exact ((hf.mul hg).const_mul (2*t)).intervalIntegrable _ _
    · exact ((hf.pow 2).add ((hf.mul hg).const_mul (2*t))).intervalIntegrable _ _
    · exact ((hg.pow 2).const_mul (t*t)).intervalIntegrable _ _
  have hdisc := discrim_le_zero hpoly
  dsimp [discrim] at hdisc
  change B^2 ≤ A*C
  nlinarith

theorem interval_integral_abs_mul_le {f g : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hab : a ≤ b) :
    (∫ s in a..b, |f s * g s|) ≤
      Real.sqrt (∫ s in a..b, f s ^ 2) * Real.sqrt (∫ s in a..b, g s ^ 2) := by
  have h := interval_integral_mul_sq_le hf.abs hg.abs hab
  simp only [sq_abs] at h
  have hA := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab (fun s => sq_nonneg (f s))
  have hB := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab (fun s => sq_nonneg (g s))
  have hI := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab
    (fun s => abs_nonneg (f s*g s))
  have hAs := Real.sq_sqrt hA
  have hBs := Real.sq_sqrt hB
  have hAB : (Real.sqrt (∫ s in a..b, f s^2) *
      Real.sqrt (∫ s in a..b, g s^2))^2 =
      (∫ s in a..b, f s^2)*(∫ s in a..b, g s^2) := by
    rw [mul_pow, hAs, hBs]
  have hn := mul_nonneg (Real.sqrt_nonneg (∫ s in a..b, f s^2))
    (Real.sqrt_nonneg (∫ s in a..b, g s^2))
  rw [show (fun s => |f s| * |g s|) = (fun s => |f s*g s|) by
    funext s; exact (abs_mul _ _).symm] at h
  nlinarith

end LengthGrowth

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`LengthGrowth).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"LengthGrowth interval-L2 audit passed for {checked} declarations."
