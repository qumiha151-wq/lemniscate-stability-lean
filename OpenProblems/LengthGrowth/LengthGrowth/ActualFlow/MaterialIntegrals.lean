import LengthGrowth.ActualFlow.IntrinsicCurve
import LengthGrowth.IntervalL2

/-! Actual geometric integrals over a fixed material parameter interval.
The material density is retained in every integral. The length-rate quantity
is a definition here; its equality to an actual time derivative is proved in
the later first-variation module, not assumed by this spatial lemma. -/

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace LengthGrowth.ActualFlow

def materialLength (γ : ℝ → ℂ) (P : ℝ) : ℝ :=
  ∫ u in 0..P, speed γ u

def materialEnergy (γ : ℝ → ℂ) (P : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ u in 0..P, curvature γ u ^ 2 * speed γ u

def materialDissipation (γ : ℝ → ℂ) (P : ℝ) : ℝ :=
  ∫ u in 0..P, force γ u ^ 2 * speed γ u

def materialLengthRate (γ : ℝ → ℂ) (P : ℝ) : ℝ :=
  ∫ u in 0..P, curvature γ u * force γ u * speed γ u

theorem materialLength_nonneg (γ : ℝ → ℂ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ materialLength γ P :=
  intervalIntegral.integral_nonneg_of_forall hP (fun u => norm_nonneg (deriv γ u))

theorem materialEnergy_nonneg (γ : ℝ → ℂ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ materialEnergy γ P := by
  apply mul_nonneg (by norm_num)
  exact intervalIntegral.integral_nonneg_of_forall hP
    (fun u => mul_nonneg (sq_nonneg (curvature γ u)) (norm_nonneg (deriv γ u)))

theorem materialDissipation_nonneg (γ : ℝ → ℂ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ materialDissipation γ P :=
  intervalIntegral.integral_nonneg_of_forall hP
    (fun u => mul_nonneg (sq_nonneg (force γ u)) (norm_nonneg (deriv γ u)))

/-- Cauchy--Schwarz with the genuine material speed as a weight. -/
theorem materialLengthRate_sq_le {γ : ℝ → ℂ} {P : ℝ}
    (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0) (hP : 0 ≤ P) :
    materialLengthRate γ P ^ 2 ≤
      2 * materialEnergy γ P * materialDissipation γ P := by
  have hs : Continuous (fun u => Real.sqrt (speed γ u)) :=
    (speed_smooth hγ hreg).continuous.sqrt
  have hk := (curvature_smooth hγ hreg).continuous
  have hF := (force_smooth hγ hreg).continuous
  have h := LengthGrowth.interval_integral_mul_sq_le (hk.mul hs) (hF.mul hs) hP
  simp only [Pi.mul_apply] at h
  have hp : (fun u => (curvature γ u * Real.sqrt (speed γ u)) *
      (force γ u * Real.sqrt (speed γ u))) =
      (fun u => curvature γ u * force γ u * speed γ u) := by
    funext u
    calc
      _ = curvature γ u * force γ u * Real.sqrt (speed γ u) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (speed_pos hreg u).le]
  have hks : (fun u => (curvature γ u * Real.sqrt (speed γ u)) ^ 2) =
      (fun u => curvature γ u ^ 2 * speed γ u) := by
    funext u
    rw [mul_pow, Real.sq_sqrt (speed_pos hreg u).le]
  have hFs : (fun u => (force γ u * Real.sqrt (speed γ u)) ^ 2) =
      (fun u => force γ u ^ 2 * speed γ u) := by
    funext u
    rw [mul_pow, Real.sq_sqrt (speed_pos hreg u).le]
  rw [hp, hks, hFs] at h
  calc
    materialLengthRate γ P ^ 2 ≤
        (∫ u in 0..P, curvature γ u ^ 2 * speed γ u) *
          (∫ u in 0..P, force γ u ^ 2 * speed γ u) := h
    _ = 2 * materialEnergy γ P * materialDissipation γ P := by
      dsimp [materialEnergy, materialDissipation]
      ring

end LengthGrowth.ActualFlow

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (n, _) in (← getEnv).constants do
    if (`LengthGrowth.ActualFlow).isPrefixOf n then
      for a in (← collectAxioms n) do
        unless allowed.contains a do throwError "Unexpected axiom {a} in {n}"
      count := count + 1
  logInfo m!"Actual material integrals: {count} declarations, standard axioms only."
