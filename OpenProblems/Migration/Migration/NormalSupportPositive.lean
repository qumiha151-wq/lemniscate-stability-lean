import Migration.NormalRegression
import Mathlib.Algebra.Field.Periodic
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Positive normal-distance energy for any center of an actual smooth
periodic unit-speed curve. A maximum of actual squared distance supplies
the proof; no force, Frenet system, or virial identity is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Matrix
open scoped ContDiff
namespace MigrationGeometry

theorem exists_normalSupport_ne_zero {x y : ℝ → ℝ} {L : ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hL : 0 < L) (hpx : Function.Periodic x L) (hpy : Function.Periodic y L)
    (hunit : ∀ s ∈ Icc 0 L, (deriv x s)^2+(deriv y s)^2=1)
    (d : Fin 2 → ℝ) :
    ∃ s ∈ Icc 0 L, normalSupport x y d s ≠ 0 := by
  by_contra hn
  push Not at hn
  let r2 : ℝ → ℝ := fun s => (x s-d 0)^2+(y s-d 1)^2
  have hr : Continuous r2 :=
    ((hx.continuous.sub continuous_const).pow 2).add
      ((hy.continuous.sub continuous_const).pow 2)
  have hpr : Function.Periodic r2 L := by
    intro s
    dsimp [r2]
    rw [hpx s,hpy s]
  obtain ⟨s,hs,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0:ℝ) L).Nonempty from ⟨0,le_rfl,hL.le⟩) hr.continuousOn
  have hglobal : ∀ t, r2 t ≤ r2 s := by
    intro t
    obtain ⟨u,hu,he⟩ := hpr.exists_mem_Ico₀ hL t
    rw [he]
    exact hmax ⟨hu.1,hu.2.le⟩
  have hloc : IsLocalMax r2 s := Filter.Eventually.of_forall hglobal
  have hd := (((hx.differentiable (by simp) s).hasDerivAt.sub_const (d 0)).pow 2).add
    (((hy.differentiable (by simp) s).hasDerivAt.sub_const (d 1)).pow 2)
  norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one] at hd
  have hq : (x s-d 0)*deriv x s+(y s-d 1)*deriv y s=0 := by
    have hz := hloc.hasDerivAt_eq_zero hd
    linarith
  have hid : (normalSupport x y d s)^2+
      ((x s-d 0)*deriv x s+(y s-d 1)*deriv y s)^2=r2 s := by
    dsimp [normalSupport,r2]
    linear_combination ((x s-d 0)^2+(y s-d 1)^2)*(hunit s hs)
  rw [hn s hs,hq] at hid
  have hs0 : r2 s=0 := by nlinarith
  have hxconst : x=fun _ => d 0 := by
    funext t
    have ht := hglobal t
    rw [hs0] at ht
    dsimp [r2] at ht
    have hz : (x t-d 0)^2=0 := by nlinarith [sq_nonneg (y t-d 1)]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  have hyconst : y=fun _ => d 1 := by
    funext t
    have ht := hglobal t
    rw [hs0] at ht
    dsimp [r2] at ht
    have hz : (y t-d 1)^2=0 := by nlinarith [sq_nonneg (x t-d 0)]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  have hu := hunit 0 ⟨le_rfl,hL.le⟩
  rw [hxconst,hyconst] at hu
  simp at hu

/-- The actual integrated squared normal distance is strictly positive
at every center, including the inverse-defined regression center. -/
theorem normalDistanceSquared_pos {x y : ℝ → ℝ} {L : ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hL : 0 < L) (hpx : Function.Periodic x L) (hpy : Function.Periodic y L)
    (hunit : ∀ s ∈ Icc 0 L, (deriv x s)^2+(deriv y s)^2=1)
    (d : Fin 2 → ℝ) : 0 < normalDistanceSquared x y L d := by
  obtain ⟨s,hs,hn⟩ := exists_normalSupport_ne_zero hx hy hL hpx hpy hunit d
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ : ℝ => (0:ℝ)) (g := fun s => (normalSupport x y d s)^2)
    hL continuous_const.continuousOn
    ((normalSupport_continuous hx hy d).pow 2).continuousOn
    (fun s _ => sq_nonneg _) ⟨s,hs,sq_pos_of_ne_zero hn⟩
  simpa only [intervalIntegral.integral_zero,normalDistanceSquared] using h

theorem regressionCenter_distance_pos {x y : ℝ → ℝ} {L : ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hL : 0 < L) (hpx : Function.Periodic x L) (hpy : Function.Periodic y L)
    (hunit : ∀ s ∈ Icc 0 L, (deriv x s)^2+(deriv y s)^2=1) :
    0 < normalDistanceSquared x y L (regressionCenter x y L) :=
  normalDistanceSquared_pos hx hy hL hpx hpy hunit _

end MigrationGeometry

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`MigrationGeometry).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains a do
          throwError "Normal support positivity audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Normal support positivity audit passed for {count} declarations; standard axioms only."
