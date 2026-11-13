module

public import SolitonClassification.Rotating.RotatingPeriodicSmooth
public import SolitonClassification.SupportODE
public import SolitonClassification.OneSignCurvature

@[expose] public section

/-! Physical support variables and actual planar position, extracted
from the global original ODE. Normalized v/8 is unscaled explicitly.
This module derives the soliton equation and regularity; periodicity is
obtained from endpoint matching, rather than added to the input. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

def rotatingK (a : State) (s : ℝ) : ℝ := rotatingTrajectory a s 0
def rotatingV (a : State) (s : ℝ) : ℝ := 8*rotatingTrajectory a s 1
def rotatingP (a : State) (s : ℝ) : ℝ := rotatingTrajectory a s 2
def rotatingQ (a : State) (s : ℝ) : ℝ := rotatingTrajectory a s 3
def rotatingAngle (a : State) (s : ℝ) : ℝ := rotatingTrajectory a s 5
def rotatingX (a : State) : ℝ → ℝ := ClosedSimilarity.profileX (rotatingP a) (rotatingQ a) (rotatingAngle a)
def rotatingY (a : State) : ℝ → ℝ := ClosedSimilarity.profileY (rotatingP a) (rotatingQ a) (rotatingAngle a)

theorem rotatingK_derivative {a : State} (htube : ∀s,rotatingTrajectory a s∈outerTube) (s : ℝ) :
    HasDerivAt (rotatingK a) (rotatingV a s) s := rotatingTrajectory_original_coordinate htube 0 s

theorem rotatingV_derivative {a : State} (htube : ∀s,rotatingTrajectory a s∈outerTube) (s : ℝ) :
    HasDerivAt (rotatingV a) (-(rotatingK a s)^3/2-rotatingP a s-a 4*rotatingQ a s) s := by
  convert! (rotatingTrajectory_original_coordinate htube 1 s).const_mul 8 using 1
  dsimp [field,rotatingK,rotatingP,rotatingQ]
  rw [rotatingTrajectory_parameter_constant]
  ring

theorem rotatingP_derivative {a : State} (htube : ∀s,rotatingTrajectory a s∈outerTube) (s : ℝ) :
    HasDerivAt (rotatingP a) (-rotatingK a s*rotatingQ a s) s := rotatingTrajectory_original_coordinate htube 2 s

theorem rotatingQ_derivative {a : State} (htube : ∀s,rotatingTrajectory a s∈outerTube) (s : ℝ) :
    HasDerivAt (rotatingQ a) (1+rotatingK a s*rotatingP a s) s := rotatingTrajectory_original_coordinate htube 3 s

theorem rotatingAngle_derivative {a : State} (htube : ∀s,rotatingTrajectory a s∈outerTube) (s : ℝ) :
    HasDerivAt (rotatingAngle a) (rotatingK a s) s := rotatingTrajectory_original_coordinate htube 5 s

def periodicRotatingSupport {a : State} {T d : ℝ} (hT : 0<T)
    (hmatch : rotatingTrajectory a T=rotatingTrajectory a (-T)+angleVector d)
    (htube : ∀s∈Icc (-T) T,rotatingTrajectory a s∈outerTube) :
    ClosedSimilarity.PeriodicSupportProfile 1 (a 4) (2*T) where
  k := rotatingK a
  v := rotatingV a
  p := rotatingP a
  q := rotatingQ a
  dk := rotatingK_derivative (rotatingTrajectory_global_tube hT hmatch htube)
  dv := by
    intro s
    simpa only [one_mul] using rotatingV_derivative (rotatingTrajectory_global_tube hT hmatch htube) s
  dp := rotatingP_derivative (rotatingTrajectory_global_tube hT hmatch htube)
  dq := rotatingQ_derivative (rotatingTrajectory_global_tube hT hmatch htube)
  periodic_k := rotatingTrajectory_coordinate_periodic hmatch 0 (by decide)
  periodic_v := by
    intro s
    dsimp [rotatingV]
    exact congrArg (fun x : ℝ => 8*x) (rotatingTrajectory_coordinate_periodic hmatch 1 (by decide) s)
  periodic_p := rotatingTrajectory_coordinate_periodic hmatch 2 (by decide)
  periodic_q := rotatingTrajectory_coordinate_periodic hmatch 3 (by decide)

theorem rotating_position_smooth {a : State}
    (htube : ∀s,rotatingTrajectory a s∈outerTube) :
    ContDiff ℝ ∞ (rotatingK a) ∧ ContDiff ℝ ∞ (rotatingV a) ∧
    ContDiff ℝ ∞ (rotatingP a) ∧ ContDiff ℝ ∞ (rotatingQ a) ∧
    ContDiff ℝ ∞ (rotatingAngle a) ∧ ContDiff ℝ ∞ (rotatingX a) ∧ ContDiff ℝ ∞ (rotatingY a) := by
  have h := contDiff_pi.mp (rotatingTrajectory_smooth_of_global_tube htube)
  have hk : ContDiff ℝ ∞ (rotatingK a) := h 0
  have hv : ContDiff ℝ ∞ (rotatingV a) := contDiff_const.mul (h 1)
  have hp : ContDiff ℝ ∞ (rotatingP a) := h 2
  have hq : ContDiff ℝ ∞ (rotatingQ a) := h 3
  have htheta : ContDiff ℝ ∞ (rotatingAngle a) := h 5
  exact ⟨hk,hv,hp,hq,htheta,(hq.mul htheta.cos).sub (hp.mul htheta.sin),
    (hq.mul htheta.sin).add (hp.mul htheta.cos)⟩

theorem rotating_position_derivatives {a : State}
    (htube : ∀s,rotatingTrajectory a s∈outerTube) (s : ℝ) :
    HasDerivAt (rotatingX a) (Real.cos (rotatingAngle a s)) s ∧
      HasDerivAt (rotatingY a) (Real.sin (rotatingAngle a s)) s :=
  ⟨ClosedSimilarity.profileX_hasDerivAt _ _ _ _ s (rotatingP_derivative htube s)
    (rotatingQ_derivative htube s) (rotatingAngle_derivative htube s),
   ClosedSimilarity.profileY_hasDerivAt _ _ _ _ s (rotatingP_derivative htube s)
    (rotatingQ_derivative htube s) (rotatingAngle_derivative htube s)⟩

theorem rotating_position_unit_speed {a : State}
    (htube : ∀s,rotatingTrajectory a s∈outerTube) (s : ℝ) :
    deriv (rotatingX a) s^2+deriv (rotatingY a) s^2=1 :=
  ClosedSimilarity.profile_unit_speed _ _ _ _ s (rotatingP_derivative htube s)
    (rotatingQ_derivative htube s) (rotatingAngle_derivative htube s)

theorem rotating_position_curvature {a : State}
    (htube : ∀s,rotatingTrajectory a s∈outerTube) (s : ℝ) :
    deriv (rotatingX a) s*deriv (deriv (rotatingY a)) s-
      deriv (rotatingY a) s*deriv (deriv (rotatingX a)) s=rotatingK a s :=
  ClosedSimilarity.profile_signed_curvature _ _ _ _ (rotatingP_derivative htube)
    (rotatingQ_derivative htube) (rotatingAngle_derivative htube) s

theorem rotating_support_force {a : State}
    (htube : ∀s,rotatingTrajectory a s∈outerTube) (s : ℝ) :
    deriv (deriv (rotatingK a)) s+(rotatingK a s)^3/2=-rotatingP a s-a 4*rotatingQ a s := by
  have hk : deriv (rotatingK a)=rotatingV a := funext fun t => (rotatingK_derivative htube t).deriv
  rw [hk,(rotatingV_derivative htube s).deriv]
  ring

theorem rotating_position_intrinsic_soliton {a : State}
    (htube : ∀s,rotatingTrajectory a s∈outerTube) (s : ℝ) :
    deriv (deriv (rotatingK a)) s+(rotatingK a s)^3/2=
      -(rotatingX a s*(-deriv (rotatingY a) s)+rotatingY a s*deriv (rotatingX a) s)-
      a 4*(rotatingX a s*deriv (rotatingX a) s+rotatingY a s*deriv (rotatingY a) s) := by
  obtain ⟨hx,hy⟩ := rotating_position_derivatives htube s
  rw [hx.deriv,hy.deriv]
  exact ClosedSimilarity.profile_soliton_equation (a 4) _ _ _ _ _
    (rotatingK_derivative htube) (rotatingV_derivative htube) s

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name || (`ClosedSimilarity).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating actual periodic-support profile audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating actual periodic-support profile audit passed for {count} declarations."
