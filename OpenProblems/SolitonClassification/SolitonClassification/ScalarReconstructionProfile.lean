import SolitonClassification.ScalarReconstructionGlobal
import SolitonClassification.SupportODE
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Actual unit-speed profile reconstructed from a scalar solution. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff
namespace ClosedSimilarity.ScalarReconstruction

def normalCoefficient (k : ℝ → ℝ) (a b s₀ s : ℝ) : ℝ :=
  (-a*force k s-b*candidateSupport k a b s₀ s)/(a^2+b^2)

def tangentCoefficient (k : ℝ → ℝ) (a b s₀ s : ℝ) : ℝ :=
  (-b*force k s+a*candidateSupport k a b s₀ s)/(a^2+b^2)

def curvatureAngle (k : ℝ → ℝ) (s : ℝ) : ℝ := ∫ u in 0..s, k u

theorem force_hasDerivAt_reconstructed {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    {a b : ℝ} (hS : ScalarEquation k a b) (s₀ : ℝ) (hanchor : k s₀≠0) (s : ℝ) :
    HasDerivAt (force k) (k s*candidateSupport k a b s₀ s-b) s := by
  have he := candidateSupport_eq_quotient_global hk hS s₀ hanchor s
  have hd : deriv (force k) s=k s*candidateSupport k a b s₀ s-b := by
    dsimp only [numerator] at he
    linarith
  rw [← hd]
  exact ((force_smooth hk).differentiable (by simp) s).hasDerivAt

theorem normalCoefficient_hasDerivAt {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    {a b : ℝ} (hS : ScalarEquation k a b) (s₀ : ℝ) (hanchor : k s₀≠0)
    (s : ℝ) :
    HasDerivAt (normalCoefficient k a b s₀)
      (-k s*tangentCoefficient k a b s₀ s) s := by
  have hf := force_hasDerivAt_reconstructed hk hS s₀ hanchor s
  have hh := candidateSupport_hasDerivAt hk a b s₀ s
  convert ((hf.const_mul (-a)).sub (hh.const_mul b)).div_const (a^2+b^2) using 1 <;>
    first | rfl | (simp only [tangentCoefficient,supportDerivative]; ring)

theorem tangentCoefficient_hasDerivAt {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    {a b : ℝ} (hS : ScalarEquation k a b) (s₀ : ℝ) (hanchor : k s₀≠0)
    (hden : a^2+b^2≠0) (s : ℝ) :
    HasDerivAt (tangentCoefficient k a b s₀)
      (1+k s*normalCoefficient k a b s₀ s) s := by
  have hf := force_hasDerivAt_reconstructed hk hS s₀ hanchor s
  have hh := candidateSupport_hasDerivAt hk a b s₀ s
  convert ((hf.const_mul (-b)).add (hh.const_mul a)).div_const (a^2+b^2) using 1 <;>
    first | rfl | (simp only [normalCoefficient,supportDerivative]; field_simp; ring)

theorem force_eq_coefficients (k : ℝ → ℝ) (a b s₀ s : ℝ) (hden : a^2+b^2≠0) :
    force k s=-a*normalCoefficient k a b s₀ s-b*tangentCoefficient k a b s₀ s := by
  dsimp only [normalCoefficient,tangentCoefficient]
  field_simp
  ring

theorem curvatureAngle_hasDerivAt {k : ℝ → ℝ} (hk : Continuous k) (s : ℝ) :
    HasDerivAt (curvatureAngle k) (k s) s :=
  intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable 0 s)
    hk.aestronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt

theorem curvatureAngle_smooth {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k) :
    ContDiff ℝ ∞ (curvatureAngle k) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun s => (curvatureAngle_hasDerivAt hk.continuous s).differentiableAt,?_⟩
  have he : deriv (curvatureAngle k)=k :=
    funext fun s => (curvatureAngle_hasDerivAt hk.continuous s).deriv
  rw [he]
  exact hk

theorem curvatureAngle_period_shift {k : ℝ → ℝ} (hk : Continuous k)
    {L : ℝ} (hp : Function.Periodic k L) (s : ℝ) :
    curvatureAngle k (s+L)=curvatureAngle k s+∫ u in 0..L, k u := by
  simpa only [curvatureAngle,zero_add] using
    hp.intervalIntegral_add_eq_add 0 s (fun x y => hk.intervalIntegrable x y)

end ClosedSimilarity.ScalarReconstruction

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`ClosedSimilarity).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Scalar profile audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Scalar profile audit passed for {count} declarations."
