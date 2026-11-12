import SolitonClassification.Rotating.RotatingNormalEvolutionScalar
import SolitonClassification.Rotating.RotatingClosedProfileClosure

/-! The scalar reparameterization field is constructed from the ACTUAL
position derivatives of a closed profile, not supplied as an ODE premise. -/
namespace SolitonClassification.Rotating.NormalEvolution
noncomputable section
open Set Real
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

def normalSupport (x y : ℝ → ℝ) (s : ℝ) : ℝ :=
  x s*(-deriv y s)+y s*deriv x s

def tangentSupport (x y : ℝ → ℝ) (s : ℝ) : ℝ :=
  x s*deriv x s+y s*deriv y s

def reparamVelocity (b : ℝ) (x y : ℝ → ℝ) (s : ℝ) : ℝ :=
  b*normalSupport x y s-tangentSupport x y s

theorem reparamVelocity_smooth (b : ℝ) {x y : ℝ → ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y) :
    ContDiff ℝ ∞ (reparamVelocity b x y) :=
  (contDiff_const.mul ((hx.mul hy.deriv'.neg).add (hy.mul hx.deriv'))).sub
    ((hx.mul hx.deriv').add (hy.mul hy.deriv'))

theorem reparamVelocity_periodic (b : ℝ) {x y : ℝ → ℝ} {L : ℝ}
    (hx : Function.Periodic x L) (hy : Function.Periodic y L) :
    Function.Periodic (reparamVelocity b x y) L := by
  intro s
  simp only [reparamVelocity,normalSupport,tangentSupport,hx s,hy s,
    periodic_deriv hx s,periodic_deriv hy s]

def profileReparamField (b : ℝ) (x y : ℝ → ℝ) (L : ℝ) (hL : 0<L)
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hpx : Function.Periodic x L) (hpy : Function.Periodic y L) : PeriodicScalarField where
  period := L
  period_pos := hL
  toFun := reparamVelocity b x y
  smooth := reparamVelocity_smooth b hx hy
  periodic := reparamVelocity_periodic b hpx hpy

def rotatingReparamField (a : State) (L : ℝ) (h : IsClosedRotatingProfile a L) : PeriodicScalarField :=
  profileReparamField (a 4) (rotatingX a) (rotatingY a) L h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1

theorem rotatingReparamField_apply (a : State) (L : ℝ) (h : IsClosedRotatingProfile a L) (s : ℝ) :
    rotatingReparamField a L h s=
      a 4*normalSupport (rotatingX a) (rotatingY a) s-tangentSupport (rotatingX a) (rotatingY a) s := rfl

theorem normal_velocity_algebra_x (b x y dx dy : ℝ) (hu : dx^2+dy^2=1) :
    x-b*y+(b*(x*(-dy)+y*dx)-(x*dx+y*dy))*dx=
      -(x*(-dy)+y*dx+b*(x*dx+y*dy))*dy := by
  linear_combination (b*y-x)*hu

theorem normal_velocity_algebra_y (b x y dx dy : ℝ) (hu : dx^2+dy^2=1) :
    y+b*x+(b*(x*(-dy)+y*dx)-(x*dx+y*dy))*dy=
      (x*(-dy)+y*dx+b*(x*dx+y*dy))*dx := by
  linear_combination -(y+b*x)*hu

end
end SolitonClassification.Rotating.NormalEvolution

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name || (`ClosedSimilarity).isPrefixOf name then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Actual profile reparameterization-field audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Actual profile reparameterization field audited: {count} declarations; standard axioms only."
