import LengthGrowth.ActualFlow.IntrinsicCurve
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! A moving immersion whose only geometric data are its actual position.
All frame, velocity and curvature fields below are definitions or consequences.
This file contains regularity, not assumed time-variation identities. -/

noncomputable section
open Set
open scoped ContDiff ComplexConjugate
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ActualFlow

structure SmoothPeriodicImmersion (I : Set ℝ) where
  time_open : IsOpen I
  period : ℝ
  period_pos : 0 < period
  position : ℝ → ℝ → ℂ
  joint_smooth : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => position z.1 z.2)
    (I ×ˢ (univ : Set ℝ))
  periodic : ∀ t ∈ I, Function.Periodic (position t) period
  immersion : ∀ t ∈ I, ∀ u, deriv (position t) u ≠ 0

section JointHelpers
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {I : Set ℝ} {f : ℝ → ℝ → E}

theorem joint_smooth_space_slice
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => f z.1 z.2) (I ×ˢ (univ : Set ℝ)))
    {t : ℝ} (ht : t ∈ I) : ContDiff ℝ ∞ (f t) :=
  hf.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun _ => ⟨ht, mem_univ _⟩)

theorem joint_smooth_time_slice
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => f z.1 z.2) (I ×ˢ (univ : Set ℝ)))
    (u : ℝ) : ContDiffOn ℝ ∞ (fun t => f t u) I :=
  hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ ht => ⟨ht, mem_univ u⟩)

theorem joint_smooth_deriv_space (hI : IsOpen I)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => f z.1 z.2) (I ×ˢ (univ : Set ℝ))) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => deriv (f z.1) z.2) (I ×ˢ (univ : Set ℝ)) := by
  have hS : IsOpen (I ×ˢ (univ : Set ℝ)) := hI.prod isOpen_univ
  have hp : ContDiffOn ℝ ∞
      (fun z : ℝ × ℝ => fderiv ℝ (fun w : ℝ × ℝ => f w.1 w.2) z (0, 1))
      (I ×ˢ (univ : Set ℝ)) :=
    (hf.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const
  apply hp.congr
  intro z hz
  have hd := (hf.differentiableOn (by simp) z hz).differentiableAt (hS.mem_nhds hz)
  exact (hd.hasFDerivAt.comp_hasDerivAt z.2
    ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))).deriv

theorem joint_smooth_deriv_time (hI : IsOpen I)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => f z.1 z.2) (I ×ˢ (univ : Set ℝ))) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => deriv (fun t => f t z.2) z.1)
      (I ×ˢ (univ : Set ℝ)) := by
  have hS : IsOpen (I ×ˢ (univ : Set ℝ)) := hI.prod isOpen_univ
  have hp : ContDiffOn ℝ ∞
      (fun z : ℝ × ℝ => fderiv ℝ (fun w : ℝ × ℝ => f w.1 w.2) z (1, 0))
      (I ×ˢ (univ : Set ℝ)) :=
    (hf.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const
  apply hp.congr
  intro z hz
  have hd := (hf.differentiableOn (by simp) z hz).differentiableAt (hS.mem_nhds hz)
  exact (hd.hasFDerivAt.comp_hasDerivAt z.1
    ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))).deriv

theorem joint_smooth_time_hasDerivAt (hI : IsOpen I)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => f z.1 z.2) (I ×ˢ (univ : Set ℝ)))
    {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    HasDerivAt (fun x => f x u) (deriv (fun x => f x u) t) t :=
  (((joint_smooth_time_slice hf u).differentiableOn (by simp) t ht).differentiableAt
    (hI.mem_nhds ht)).hasDerivAt

end JointHelpers

namespace SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

def velocity (t u : ℝ) : ℂ := deriv (fun x => c.position x u) t

/-- The tangent component of the actual arclength derivative of velocity. -/
def velocityGradientTangent (t u : ℝ) : ℝ :=
  inner ℝ (arcDerivative (c.position t) (c.velocity t) u) (tangent (c.position t) u)

/-- The normal component of the actual arclength derivative of velocity. -/
def velocityGradientNormal (t u : ℝ) : ℝ :=
  inner ℝ (arcDerivative (c.position t) (c.velocity t) u) (normal (c.position t) u)

theorem position_slice_smooth {t : ℝ} (ht : t ∈ I) : ContDiff ℝ ∞ (c.position t) :=
  joint_smooth_space_slice c.joint_smooth ht

theorem velocity_joint_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => c.velocity z.1 z.2) (I ×ˢ (univ : Set ℝ)) :=
  joint_smooth_deriv_time c.time_open c.joint_smooth

theorem velocity_slice_smooth {t : ℝ} (ht : t ∈ I) : ContDiff ℝ ∞ (c.velocity t) :=
  joint_smooth_space_slice c.velocity_joint_smooth ht

theorem position_time_hasDerivAt {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    HasDerivAt (fun x => c.position x u) (c.velocity t u) t :=
  joint_smooth_time_hasDerivAt c.time_open c.joint_smooth ht u

theorem speed_joint_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => speed (c.position z.1) z.2) (I ×ˢ (univ : Set ℝ)) :=
  (joint_smooth_deriv_space c.time_open c.joint_smooth).norm ℝ
    (fun z hz => c.immersion z.1 hz.1 z.2)

theorem arcDerivative_joint_smooth {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → ℝ → E}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => f z.1 z.2) (I ×ˢ (univ : Set ℝ))) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => arcDerivative (c.position z.1) (f z.1) z.2)
      (I ×ˢ (univ : Set ℝ)) :=
  (c.speed_joint_smooth.inv (fun z hz => (speed_pos (c.immersion z.1 hz.1) z.2).ne')).smul
    (joint_smooth_deriv_space c.time_open hf)

theorem tangent_joint_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => tangent (c.position z.1) z.2) (I ×ˢ (univ : Set ℝ)) :=
  c.arcDerivative_joint_smooth c.joint_smooth

theorem normal_joint_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => normal (c.position z.1) z.2) (I ×ˢ (univ : Set ℝ)) :=
  contDiffOn_const.mul c.tangent_joint_smooth

theorem curvature_joint_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => curvature (c.position z.1) z.2) (I ×ˢ (univ : Set ℝ)) := by
  have hnum := Complex.imCLM.contDiff.comp_contDiffOn
    ((Complex.conjCLE.contDiff.comp_contDiffOn c.tangent_joint_smooth).mul
      (joint_smooth_deriv_space (f := fun t => tangent (c.position t))
        c.time_open c.tangent_joint_smooth))
  exact hnum.div c.speed_joint_smooth
    (fun z hz => (speed_pos (c.immersion z.1 hz.1) z.2).ne')

theorem curvatureGradient_joint_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => curvatureGradient (c.position z.1) z.2) (I ×ˢ (univ : Set ℝ)) :=
  c.arcDerivative_joint_smooth (f := fun t => curvature (c.position t)) c.curvature_joint_smooth

theorem curvatureSecond_joint_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => curvatureSecond (c.position z.1) z.2) (I ×ˢ (univ : Set ℝ)) :=
  c.arcDerivative_joint_smooth (f := fun t => curvatureGradient (c.position t))
    c.curvatureGradient_joint_smooth

theorem force_joint_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => force (c.position z.1) z.2) (I ×ˢ (univ : Set ℝ)) :=
  c.curvatureSecond_joint_smooth.add ((c.curvature_joint_smooth.pow 3).div_const 2)

theorem stress_joint_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => stress (c.position z.1) z.2) (I ×ˢ (univ : Set ℝ)) := by
  exact ((((Complex.ofRealCLM.contDiff.comp_contDiffOn c.curvature_joint_smooth).pow 2).div_const 2).mul
    c.tangent_joint_smooth).add
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn c.curvatureGradient_joint_smooth).mul
      c.normal_joint_smooth)

theorem velocityGradientTangent_joint_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => c.velocityGradientTangent z.1 z.2) (I ×ˢ (univ : Set ℝ)) :=
  (c.arcDerivative_joint_smooth c.velocity_joint_smooth).inner ℝ c.tangent_joint_smooth

theorem velocityGradientNormal_joint_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => c.velocityGradientNormal z.1 z.2) (I ×ˢ (univ : Set ℝ)) :=
  (c.arcDerivative_joint_smooth c.velocity_joint_smooth).inner ℝ c.normal_joint_smooth

end SmoothPeriodicImmersion
end LengthGrowth.ActualFlow

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`LengthGrowth.ActualFlow).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Family regularity audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Family regularity audit passed: {checked} declarations; standard axioms only."
