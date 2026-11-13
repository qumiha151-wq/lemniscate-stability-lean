module

public import SolitonClassification.Rotating.RotatingClosedProfile

@[expose] public section

/-! Rational angle holonomy closes the actual reconstructed position.
Periodicity of the support and the angle shift are derived from exact
ODE endpoint matching. No geometric closure is an input. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem rotating_position_periodic {a : State} {T d : ℝ}
    (hmatch : rotatingTrajectory a T=rotatingTrajectory a (-T)+angleVector d)
    (n : ℕ) (m : ℤ) (hhol : (n:ℝ)*d=(m:ℝ)*(2*Real.pi)) :
    Function.Periodic (rotatingX a) ((n:ℝ)*(2*T)) ∧
    Function.Periodic (rotatingY a) ((n:ℝ)*(2*T)) := by
  apply ClosedSimilarity.profile_periodic _ _ _ _ m
  · exact (rotatingTrajectory_coordinate_periodic hmatch 2 (by decide)).nat_mul n
  · exact (rotatingTrajectory_coordinate_periodic hmatch 3 (by decide)).nat_mul n
  · intro s
    have h := additive_holonomy_nat_mul (theta:=rotatingAngle a) (L:=2*T) (d:=d)
      (rotatingTrajectory_angle_shift hmatch) n s
    rw [hhol] at h
    exact h

theorem rotating_total_curvature {a : State} {T d : ℝ} (hT : 0<T)
    (hmatch : rotatingTrajectory a T=rotatingTrajectory a (-T)+angleVector d)
    (htube : ∀s∈Icc (-T) T,rotatingTrajectory a s∈outerTube)
    (n : ℕ) (m : ℤ) (hhol : (n:ℝ)*d=(m:ℝ)*(2*Real.pi)) :
    (∫ s in 0..((n:ℝ)*(2*T)),rotatingK a s)=(m:ℝ)*(2*Real.pi) := by
  have hg := rotatingTrajectory_global_tube hT hmatch htube
  have hk := (rotating_position_smooth hg).1.continuous
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => rotatingAngle_derivative hg s) (hk.intervalIntegrable _ _)]
  have h := additive_holonomy_nat_mul (theta:=rotatingAngle a) (L:=2*T) (d:=d)
    (rotatingTrajectory_angle_shift hmatch) n 0
  simp only [zero_add,hhol] at h
  change rotatingAngle a ((n:ℝ)*(2*T))-rotatingAngle a 0=(m:ℝ)*(2*Real.pi)
  linarith

/-- A property of the explicit actual position functions, not an
existential replacement curve. The curvature is computed from their
coordinate derivatives, and the soliton equation is intrinsic. -/
def IsClosedRotatingProfile (a : State) (L : ℝ) : Prop :=
  0<L ∧ ContDiff ℝ ∞ (rotatingX a) ∧ ContDiff ℝ ∞ (rotatingY a) ∧
  Function.Periodic (rotatingX a) L ∧ Function.Periodic (rotatingY a) L ∧
  (∀s,deriv (rotatingX a) s^2+deriv (rotatingY a) s^2=1) ∧
  (∀s,deriv (rotatingX a) s*deriv (deriv (rotatingY a)) s-
    deriv (rotatingY a) s*deriv (deriv (rotatingX a)) s=rotatingK a s) ∧
  (∀s,deriv (deriv (rotatingK a)) s+(rotatingK a s)^3/2=
    -(rotatingX a s*(-deriv (rotatingY a) s)+rotatingY a s*deriv (rotatingX a) s)-
    a 4*(rotatingX a s*deriv (rotatingX a) s+rotatingY a s*deriv (rotatingY a) s))

theorem closed_rotating_profile_of_endpoint {a : State} {T d : ℝ} (hT : 0<T)
    (hmatch : rotatingTrajectory a T=rotatingTrajectory a (-T)+angleVector d)
    (htube : ∀s∈Icc (-T) T,rotatingTrajectory a s∈outerTube)
    (n : ℕ) (hn : 0<n) (m : ℤ) (hhol : (n:ℝ)*d=(m:ℝ)*(2*Real.pi)) :
    IsClosedRotatingProfile a ((n:ℝ)*(2*T)) := by
  have hg := rotatingTrajectory_global_tube hT hmatch htube
  have hs := rotating_position_smooth hg
  obtain ⟨hx,hy⟩ := rotating_position_periodic hmatch n m hhol
  exact ⟨mul_pos (Nat.cast_pos.mpr hn) (by linarith),hs.2.2.2.2.2.1,hs.2.2.2.2.2.2,hx,hy,
    rotating_position_unit_speed hg,rotating_position_curvature hg,rotating_position_intrinsic_soliton hg⟩

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name || (`ClosedSimilarity).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating rational-holonomy closure audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating rational-holonomy closure audit passed for {count} declarations."
