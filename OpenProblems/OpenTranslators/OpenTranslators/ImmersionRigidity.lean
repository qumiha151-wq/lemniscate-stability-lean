import OpenTranslators.ImmersionFrenet
import OpenTranslators.ProjectedRigidity

/-! Bounded-curvature rigidity for actual arbitrary smooth unit-speed planar
immersions translating with an arbitrary nonzero velocity. No angle lift,
Frenet field, stress identity, or projected-ODE conclusion is assumed. -/

namespace OpenTranslator.Immersion
noncomputable section
open Set MeasureTheory
open scoped ContDiff

def forceProjection (x y : ℝ → ℝ) (vx vy s : ℝ) : ℝ := vx*deriv y s-vy*deriv x s
def tangentProjection (x y : ℝ → ℝ) (vx vy s : ℝ) : ℝ := vx*deriv x s+vy*deriv y s

variable {x y : ℝ → ℝ} {vx vy K : ℝ}
variable (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
variable (hunit : ∀ s, (deriv x s)^2+(deriv y s)^2=1)

include hunit in
theorem projection_norm_identity (s : ℝ) :
    forceProjection x y vx vy s ^ 2 + tangentProjection x y vx vy s ^ 2 = vx^2+vy^2 := by
  calc
    _ = (vx^2+vy^2)*((deriv x s)^2+(deriv y s)^2) := by
      dsimp [forceProjection, tangentProjection]
      ring
    _ = _ := by rw [hunit s, mul_one]

include hx hy hunit in
theorem forceProjection_hasDerivAt (s : ℝ) :
    HasDerivAt (forceProjection x y vx vy)
      (curvature x y s*tangentProjection x y vx vy s) s := by
  have hdx := ((contDiff_infty_iff_deriv.mp hx).2.differentiable (by simp) s).hasDerivAt
  have hdy := ((contDiff_infty_iff_deriv.mp hy).2.differentiable (by simp) s).hasDerivAt
  rw [frenet_x hx hy hunit s] at hdx
  rw [frenet_y hx hy hunit s] at hdy
  convert (hdy.const_mul vx).sub (hdx.const_mul vy) using 1 <;>
    first | rfl | (dsimp [tangentProjection]; ring)

include hx hy hunit in
theorem tangentProjection_hasDerivAt (s : ℝ) :
    HasDerivAt (tangentProjection x y vx vy)
      (-curvature x y s*forceProjection x y vx vy s) s := by
  have hdx := ((contDiff_infty_iff_deriv.mp hx).2.differentiable (by simp) s).hasDerivAt
  have hdy := ((contDiff_infty_iff_deriv.mp hy).2.differentiable (by simp) s).hasDerivAt
  rw [frenet_x hx hy hunit s] at hdx
  rw [frenet_y hx hy hunit s] at hdy
  convert (hdx.const_mul vx).add (hdy.const_mul vy) using 1 <;>
    first | rfl | (dsimp [forceProjection]; ring)

include hx hy hunit in
/-- The actual position curvature vanishes for any nonzero translation vector
when it is globally bounded. The force is computed by differentiating position. -/
theorem arbitrary_velocity_curvature_rigidity
    (hV : vx ≠ 0 ∨ vy ≠ 0)
    (htranslator : ∀ s, TranslatorGeometry.elasticForce x y s = forceProjection x y vx vy s)
    (hK : ∀ s, |curvature x y s| ≤ K) :
    (∀ s, curvature x y s = 0) ∧ (∀ s, forceProjection x y vx vy s = 0) := by
  have hk := curvature_smooth hx hy
  have hkd := (contDiff_infty_iff_deriv.mp hk).2
  have hL : 0 < vx^2+vy^2 := by
    rcases hV with hvx | hvy
    · nlinarith [sq_pos_of_ne_zero hvx, sq_nonneg vy]
    · nlinarith [sq_pos_of_ne_zero hvy, sq_nonneg vx]
  apply ProjectedRigidity.projected_rigidity
    (k := curvature x y) (v := deriv (curvature x y))
    (f := forceProjection x y vx vy) (q := tangentProjection x y vx vy)
    (L := vx^2+vy^2)
    (fun s => (hk.differentiable (by simp) s).hasDerivAt) ?_
    (forceProjection_hasDerivAt hx hy hunit) (tangentProjection_hasDerivAt hx hy hunit)
    hL (projection_norm_identity hunit) hK
  intro s
  have he : deriv (deriv (curvature x y)) s =
      -(curvature x y s)^3/2+forceProjection x y vx vy s := by
    have hh := htranslator s
    change deriv (deriv (curvature x y)) s + (curvature x y s)^3/2 =
      forceProjection x y vx vy s at hh
    linarith
  rw [← he]
  exact (hkd.differentiable (by simp) s).hasDerivAt

include hx hy hunit in
/-- Actual coordinates are affine with a unit direction parallel to the
nonzero velocity; translations and arbitrary tangent orientation are allowed. -/
theorem arbitrary_velocity_affine_rigidity
    (hV : vx ≠ 0 ∨ vy ≠ 0)
    (htranslator : ∀ s, TranslatorGeometry.elasticForce x y s = forceProjection x y vx vy s)
    (hK : ∀ s, |curvature x y s| ≤ K) :
    ∃ a b : ℝ, a^2+b^2=1 ∧ vx*b-vy*a=0 ∧
      ∀ s, x s=x 0+s*a ∧ y s=y 0+s*b := by
  have hr := arbitrary_velocity_curvature_rigidity hx hy hunit hV htranslator hK
  have hxx (s : ℝ) : deriv (deriv x) s = 0 := by
    rw [frenet_x hx hy hunit s, hr.1 s, neg_zero, zero_mul]
  have hyy (s : ℝ) : deriv (deriv y) s = 0 := by
    rw [frenet_y hx hy hunit s, hr.1 s, zero_mul]
  have hdx (s : ℝ) : deriv x s = deriv x 0 :=
    isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
      (fun u _ => ((contDiff_infty_iff_deriv.mp hx).2.differentiable (by simp) u).differentiableWithinAt)
      (fun u _ => by rw [hxx u]; rfl) (mem_univ s) (mem_univ 0)
  have hdy (s : ℝ) : deriv y s = deriv y 0 :=
    isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
      (fun u _ => ((contDiff_infty_iff_deriv.mp hy).2.differentiable (by simp) u).differentiableWithinAt)
      (fun u _ => by rw [hyy u]; rfl) (mem_univ s) (mem_univ 0)
  refine ⟨deriv x 0, deriv y 0, hunit 0, hr.2 0, ?_⟩
  intro s
  have hdx' (u : ℝ) : HasDerivAt x (deriv x 0) u := by
    rw [← hdx u]
    exact (hx.differentiable (by simp) u).hasDerivAt
  have hdy' (u : ℝ) : HasDerivAt y (deriv y 0) u := by
    rw [← hdy u]
    exact (hy.differentiable (by simp) u).hasDerivAt
  have hix := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := s) (fun u _ => hdx' u) (intervalIntegrable_const (c := deriv x 0))
  have hiy := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := s) (fun u _ => hdy' u) (intervalIntegrable_const (c := deriv y 0))
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hix hiy
  constructor <;> linarith

include hx hy hunit in
/-- Geometric-input version: the normal component of the actual constant
translation velocity equals minus the actual elastic force. Zero velocity is excluded. -/
theorem geometric_translator_affine_rigidity
    (hV : vx ≠ 0 ∨ vy ≠ 0)
    (hflow : ∀ s, vx*(-deriv y s)+vy*deriv x s = -TranslatorGeometry.elasticForce x y s)
    (hK : ∀ s, |curvature x y s| ≤ K) :
    ∃ a b : ℝ, a^2+b^2=1 ∧ vx*b-vy*a=0 ∧
      ∀ s, x s=x 0+s*a ∧ y s=y 0+s*b := by
  apply arbitrary_velocity_affine_rigidity hx hy hunit hV ?_ hK
  intro s
  have hh := hflow s
  dsimp [forceProjection]
  linarith

end
end OpenTranslator.Immersion

#print axioms OpenTranslator.Immersion.geometric_translator_affine_rigidity

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`OpenTranslator).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
      checked := checked + 1
  logInfo m!"ImmersionRigidity: audited {checked} declarations; standard axioms only."
