module

public import SolitonClassification.Rotating.RotatingPeriodicFlow
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-! Finite-period tube confinement extends to all times by the proved
support periodicity. The actual original-ODE identity then bootstraps
the global trajectory to C-infinity using the polynomial field. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem rotatingTrajectory_tube_periodic {a : State} {T d : ℝ}
    (hmatch : rotatingTrajectory a T=rotatingTrajectory a (-T)+angleVector d) :
    Function.Periodic (fun s => rotatingTrajectory a s∈outerTube) (2*T) := by
  intro s
  change (rotatingTrajectory a (s+2*T)∈outerTube)=(rotatingTrajectory a s∈outerTube)
  rw [rotatingTrajectory_quasiperiodic hmatch s]
  simp [outerTube,angleVector]

theorem rotatingTrajectory_global_tube {a : State} {T d : ℝ} (hT : 0<T)
    (hmatch : rotatingTrajectory a T=rotatingTrajectory a (-T)+angleVector d)
    (htube : ∀s∈Icc (-T) T,rotatingTrajectory a s∈outerTube) :
    ∀s,rotatingTrajectory a s∈outerTube := by
  intro s
  obtain ⟨u,hu,he⟩ := (rotatingTrajectory_tube_periodic hmatch).exists_mem_Ico (by linarith) s (-T)
  rw [he]
  exact htube u ⟨hu.1,by linarith [hu.2]⟩

theorem rotatingTrajectory_original_derivative {a : State}
    (htube : ∀s,rotatingTrajectory a s∈outerTube) (s : ℝ) :
    HasDerivAt (rotatingTrajectory a) (field (rotatingTrajectory a s)) s := by
  simpa only [clippedField_eq (htube s)] using rotatingTrajectory_derivative a s

theorem rotatingTrajectory_original_coordinate {a : State}
    (htube : ∀s,rotatingTrajectory a s∈outerTube) (i : Fin 6) (s : ℝ) :
    HasDerivAt (fun t => rotatingTrajectory a t i) (field (rotatingTrajectory a s) i) s := by
  convert! (ContinuousLinearMap.proj i : State →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s
    (rotatingTrajectory_original_derivative htube s) using 1

/-- Elementary smooth-ODE bootstrap, proved here without importing a
different open-problem project. Each derivative equals f composed with
the actual trajectory, so induction raises the differentiability order. -/
theorem rotatingTrajectory_smooth_of_global_tube {a : State}
    (htube : ∀s,rotatingTrajectory a s∈outerTube) : ContDiff ℝ ∞ (rotatingTrajectory a) := by
  have hd : Differentiable ℝ (rotatingTrajectory a) :=
    fun s => (rotatingTrajectory_original_derivative htube s).differentiableAt
  have he : deriv (rotatingTrajectory a)=field ∘ rotatingTrajectory a :=
    funext fun s => (rotatingTrajectory_original_derivative htube s).deriv
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hd.continuous
  | succ n ih =>
    rw [Nat.cast_succ,contDiff_succ_iff_deriv]
    refine ⟨hd,by simp,?_⟩
    rw [he]
    exact (contDiff_infty.mp field_smooth n).comp ih

theorem rotatingTrajectory_smooth {a : State} {T d : ℝ} (hT : 0<T)
    (hmatch : rotatingTrajectory a T=rotatingTrajectory a (-T)+angleVector d)
    (htube : ∀s∈Icc (-T) T,rotatingTrajectory a s∈outerTube) :
    ContDiff ℝ ∞ (rotatingTrajectory a) :=
  rotatingTrajectory_smooth_of_global_tube (rotatingTrajectory_global_tube hT hmatch htube)

theorem additive_holonomy_nat_mul {theta : ℝ → ℝ} {L d : ℝ}
    (h : ∀s,theta (s+L)=theta s+d) (n : ℕ) :
    ∀s,theta (s+(n:ℝ)*L)=theta s+(n:ℝ)*d := by
  induction n with
  | zero => intro s; simp
  | succ n ih =>
    intro s
    have he : s+((n+1:ℕ):ℝ)*L=(s+(n:ℝ)*L)+L := by push_cast; ring
    rw [he,h,ih]
    push_cast
    ring

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating all-time smooth periodic-support audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating all-time smooth periodic-support audit passed for {count} declarations."
