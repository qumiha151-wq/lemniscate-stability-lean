import SolitonClassification.ReflectedGeometry
import SolitonClassification.Rotating.RotatingPeriodicSmooth

/-! A verified quarter segment of the scaled numerical flow gives a physical
zero-turn closed expander. Tube confinement is only needed on that segment. -/
noncomputable section
namespace ClosedSimilarity.ReflectedArc
open Set
open SolitonClassification.Rotating (rotatingTrajectory outerTube)
set_option backward.isDefEq.respectTransparency false

def shootingStart (b : ℝ) : SolitonClassification.Rotating.State := ![0,b/8,0,0,0,0]
def physicalSupport (b s : ℝ) : Support :=
  let x := rotatingTrajectory (shootingStart b) s
  ![x 0,8*x 1,x 2,x 3]

theorem physicalSupport_continuous (b : ℝ) : Continuous (physicalSupport b) := by
  have c : Continuous (rotatingTrajectory (shootingStart b)) :=
    continuous_iff_continuousAt.mpr fun s =>
      (SolitonClassification.Rotating.rotatingTrajectory_derivative _ s).continuousAt
  apply continuous_pi
  intro i
  fin_cases i <;> simp [physicalSupport] <;> fun_prop

theorem physicalSupport_starts (b : ℝ) : physicalSupport b 0=![0,b,0,0] := by
  ext i
  fin_cases i <;> simp [physicalSupport,shootingStart,SolitonClassification.Rotating.rotatingTrajectory_zero]
  ring

theorem physicalSupport_deriv {b s : ℝ} (ht : rotatingTrajectory (shootingStart b) s∈outerTube) :
    HasDerivAt (physicalSupport b) (supportField (physicalSupport b s)) s := by
  let x := rotatingTrajectory (shootingStart b)
  have hd : HasDerivAt x (SolitonClassification.Rotating.field (x s)) s := by
    simpa only [SolitonClassification.Rotating.clippedField_eq ht] using
      SolitonClassification.Rotating.rotatingTrajectory_derivative (shootingStart b) s
  have h := hasDerivAt_pi.mp hd
  have hp : x s 4=0 := SolitonClassification.Rotating.rotatingTrajectory_parameter_constant _ s
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact h 0
  · convert! (h 1).const_mul 8 using 1
    change -(x s 0)^3/2-x s 2=8*(-(x s 0)^3/16-x s 2/8-x s 4*x s 3/8)
    rw [hp]
    ring
  · exact h 2
  · exact h 3

theorem expander_of_shooting_zero {b t : ℝ} (ht : 0<t)
    (tube : ∀ s∈Icc 0 t, rotatingTrajectory (shootingStart b) s∈outerTube)
    (hv : rotatingTrajectory (shootingStart b) t 1=0)
    (hq : rotatingTrajectory (shootingStart b) t 3=0) :
    Nonempty (ZeroTurnExpander (4*t) b) := by
  apply exists_zeroTurnExpander_of_quarter ht (physicalSupport_continuous b)
    (fun s hs => physicalSupport_deriv (tube s hs)) (physicalSupport_starts b) _ hq
  change 8 * rotatingTrajectory (shootingStart b) t 1 = 0
  rw [hv,mul_zero]

end ClosedSimilarity.ReflectedArc
