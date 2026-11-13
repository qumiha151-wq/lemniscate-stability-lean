import LengthGrowth.ActualFlow.JetGeometry

/-!
# The actual elastic force in terms of four spatial position jets

The expression here is proved equal to `force`, rather than used to redefine
it. This allows continuity of four spatial jets up to an initial time to
control the intrinsic force without requiring a backward time extension.
-/

noncomputable section
open Filter
open scoped ContDiff Topology

namespace LengthGrowth.ActualFlow

def jetGradientNumerator (γ : ℝ → ℂ) (u : ℝ) : ℝ :=
  jetDetFirst γ u * jetNormSq γ u - (3 / 2 : ℝ) * jetDet γ u * jetNormSqFirst γ u

variable {γ : ℝ → ℂ}

/-- The actual first arclength derivative of curvature, using three position jets. -/
theorem curvatureGradient_eq_three_jet (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) :
    curvatureGradient γ u = jetGradientNumerator γ u / speed γ u ^ 6 := by
  have hg := speed_hasDerivAt_jet hγ hreg u
  have hd := (jetDet_hasDerivAt hγ u).div (hg.pow 3)
    (pow_ne_zero 3 (speed_pos hreg u).ne')
  have he : curvature γ = (fun x => jetDet γ x / speed γ x ^ 3) :=
    funext (curvature_eq_two_jet hγ hreg)
  change HasDerivAt (fun x => jetDet γ x / speed γ x ^ 3) _ u at hd
  rw [← he] at hd
  rw [curvatureGradient, arcDerivative, hd.deriv]
  simp only [smul_eq_mul, jetGradientNumerator, jetNormSq_eq_speed_sq,
    Nat.cast_ofNat, Nat.reduceSub, Pi.pow_apply]
  field_simp [(speed_pos hreg u).ne']

theorem jetGradientNumerator_hasDerivAt (hγ : ContDiff ℝ ∞ γ) (u : ℝ) :
    HasDerivAt (jetGradientNumerator γ)
      (jetDetSecond γ u * jetNormSq γ u - (1 / 2 : ℝ) * jetDetFirst γ u * jetNormSqFirst γ u -
        (3 / 2 : ℝ) * jetDet γ u * jetNormSqSecond γ u) u := by
  have hd := ((jetDetFirst_hasDerivAt hγ u).mul (jetNormSq_hasDerivAt hγ u)).sub
    (((jetDet_hasDerivAt hγ u).const_mul (3 / 2 : ℝ)).mul
      (jetNormSqFirst_hasDerivAt hγ u))
  convert! hd using 1
  ring

/-- Four-jet formula, with `r = |gamma_u|^2` and determinant jets as defined
in `JetGeometry`. There are no independently supplied curvature derivatives. -/
theorem force_eq_four_jet (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) :
    force γ u =
      (jetDetSecond γ u * jetNormSq γ u ^ 2 -
        (7 / 2 : ℝ) * jetDetFirst γ u * jetNormSqFirst γ u * jetNormSq γ u -
        (3 / 2 : ℝ) * jetDet γ u * jetNormSqSecond γ u * jetNormSq γ u +
        (9 / 2 : ℝ) * jetDet γ u * jetNormSqFirst γ u ^ 2 + jetDet γ u ^ 3 / 2) /
      speed γ u ^ 9 := by
  have hg := speed_hasDerivAt_jet hγ hreg u
  have hd := (jetGradientNumerator_hasDerivAt hγ u).div (hg.pow 6)
    (pow_ne_zero 6 (speed_pos hreg u).ne')
  have he : curvatureGradient γ =
      (fun x => jetGradientNumerator γ x / speed γ x ^ 6) :=
    funext (curvatureGradient_eq_three_jet hγ hreg)
  change HasDerivAt (fun x => jetGradientNumerator γ x / speed γ x ^ 6) _ u at hd
  rw [← he] at hd
  rw [force, curvatureSecond, arcDerivative, hd.deriv, curvature_eq_two_jet hγ hreg]
  simp only [smul_eq_mul, jetGradientNumerator, jetNormSq_eq_speed_sq,
    Nat.cast_ofNat, Nat.reduceSub, Pi.pow_apply]
  field_simp [(speed_pos hreg u).ne']
  ring

/-- A pure expression on four complex position jets. It is only identified
with the intrinsic force by the actual derivative theorem below. -/
def fourJetForceValue (v a b c : ℂ) : ℝ :=
  let r := ‖v‖ ^ 2
  let r₁ := 2 * inner ℝ v a
  let r₂ := 2 * (inner ℝ a a + inner ℝ v b)
  let n := determinant v a
  let n₁ := determinant v b
  let n₂ := determinant a b + determinant v c
  (n₂ * r ^ 2 - (7 / 2 : ℝ) * n₁ * r₁ * r - (3 / 2 : ℝ) * n * r₂ * r +
    (9 / 2 : ℝ) * n * r₁ ^ 2 + n ^ 3 / 2) / ‖v‖ ^ 9

theorem force_eq_fourJetForceValue (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) :
    force γ u = fourJetForceValue (positionJet1 γ u) (positionJet2 γ u)
      (positionJet3 γ u) (positionJet4 γ u) :=
  force_eq_four_jet hγ hreg u

theorem determinant_tendsto {X : Type*} {l : Filter X}
    {v a : X → ℂ} {v₀ a₀ : ℂ}
    (hv : Tendsto v l (𝓝 v₀)) (ha : Tendsto a l (𝓝 a₀)) :
    Tendsto (fun x => determinant (v x) (a x)) l (𝓝 (determinant v₀ a₀)) :=
  Complex.continuous_im.continuousAt.tendsto.comp
    ((Complex.continuous_conj.continuousAt.tendsto.comp hv).mul ha)

/-- Continuity along any filter, in particular along a forward time boundary.
Only the limiting first position jet must be nonzero. -/
theorem fourJetForceValue_tendsto {X : Type*} {l : Filter X}
    {v a b c : X → ℂ} {v₀ a₀ b₀ c₀ : ℂ}
    (hv : Tendsto v l (𝓝 v₀)) (ha : Tendsto a l (𝓝 a₀))
    (hb : Tendsto b l (𝓝 b₀)) (hc : Tendsto c l (𝓝 c₀)) (hreg : v₀ ≠ 0) :
    Tendsto (fun x => fourJetForceValue (v x) (a x) (b x) (c x)) l
      (𝓝 (fourJetForceValue v₀ a₀ b₀ c₀)) := by
  have hr := hv.norm.pow 2
  have hr₁ : Tendsto (fun x => 2 * inner ℝ (v x) (a x)) l
      (𝓝 (2 * inner ℝ v₀ a₀)) := tendsto_const_nhds.mul (hv.inner ha)
  have hr₂ : Tendsto (fun x => 2 * (inner ℝ (a x) (a x) + inner ℝ (v x) (b x))) l
      (𝓝 (2 * (inner ℝ a₀ a₀ + inner ℝ v₀ b₀))) :=
    tendsto_const_nhds.mul ((ha.inner ha).add (hv.inner hb))
  have hn := determinant_tendsto hv ha
  have hn₁ := determinant_tendsto hv hb
  have hn₂ := (determinant_tendsto ha hb).add (determinant_tendsto hv hc)
  exact (((((hn₂.mul (hr.pow 2)).sub
    (((tendsto_const_nhds.mul hn₁).mul hr₁).mul hr)).sub
    (((tendsto_const_nhds.mul hn).mul hr₂).mul hr)).add
    ((tendsto_const_nhds.mul hn).mul (hr₁.pow 2))).add
    ((hn.pow 3).div_const 2)).div (hv.norm.pow 9)
      (pow_ne_zero 9 (norm_ne_zero_iff.mpr hreg))

end LengthGrowth.ActualFlow

#print axioms LengthGrowth.ActualFlow.force_eq_four_jet

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`LengthGrowth.ActualFlow).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless allowed.contains a do throwError "Four-jet force audit failed: {name} uses {a}"
      count := count + 1
  logInfo m!"ACTUAL_FOUR_JET_FORCE_AUDIT {count}: standard three axioms only."
