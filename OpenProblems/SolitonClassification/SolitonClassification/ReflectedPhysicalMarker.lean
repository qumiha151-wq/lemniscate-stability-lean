import SolitonClassification.ReflectedPureNormal
import SolitonClassification.ReflectedMarker
import SolitonClassification.CubicSupportRigidity

/-! The marker and cubic-law obstruction refer to the actual closed shooting
trajectory used as the initial slice in the pure-normal evolution. -/
noncomputable section
namespace ClosedSimilarity.ReflectedArc
open Set SolitonClassification.Rotating
set_option backward.isDefEq.respectTransparency false

theorem shooting_profile_marker {b T : ℝ} (hT : 0<T) (hb : 0<b)
    (tube : ∀ t∈Icc 0 T, rotatingTrajectory (shootingStart b) t∈outerTube)
    (hv : rotatingTrajectory (shootingStart b) T 1=0)
    (hq : rotatingTrajectory (shootingStart b) T 3=0) :
    rotatingX (shootingStart b) 0=0 ∧ rotatingY (shootingStart b) 0=0 ∧
    rotatingK (shootingStart b) 0=0 ∧ deriv (rotatingK (shootingStart b)) 0=b ∧
    (∀ s, rotatingK (shootingStart b) s=0 → rotatingX (shootingStart b) s=0 →
      rotatingY (shootingStart b) s=0 → |deriv (rotatingK (shootingStart b)) s|=b) ∧
    (b^2≠6/5 → ¬∃ a d j c : ℝ, ∀ s, rotatingP (shootingStart b) s =
      a*(rotatingK (shootingStart b) s)^3 + d*(rotatingK (shootingStart b) s)^2 +
      j*rotatingK (shootingStart b) s+c) := by
  let a₀ := shootingStart b
  obtain ⟨hm,hd⟩ := reflected_endpoint_and_tube tube hv hq
  have ht : 0<2*T := by linarith
  have allT := rotatingTrajectory_global_tube ht hm hd
  have dh := rotatingK_derivative allT 0
  have kb : rotatingK a₀ 0=0 := by simp [rotatingK,a₀,shootingStart,rotatingTrajectory_zero]
  have vb : rotatingV a₀ 0=b := by simp [rotatingV,a₀,shootingStart,rotatingTrajectory_zero]; ring
  have init := physicalSupport_starts b
  have m := ReflectedMarker.primitive_marker_of_seams
    (z:=physicalSupport b) (fun s => physicalSupport_deriv (allT s)) hb hT init
    (by change 8*rotatingTrajectory a₀ T 1=0; rw [hv,mul_zero]) hq
  obtain ⟨_,_,_,_,mark⟩ := m
  refine ⟨?_,?_,kb,dh.deriv.trans vb,?_,?_⟩
  · simp [rotatingX,profileX,rotatingP,rotatingQ,shootingStart,rotatingTrajectory_zero]
  · simp [rotatingY,profileY,rotatingP,rotatingQ,shootingStart,rotatingTrajectory_zero]
  · intro s ks xs ys
    have x := normal_support (rotatingP a₀) (rotatingQ a₀) (rotatingAngle a₀) s
    have y := tangent_support (rotatingP a₀) (rotatingQ a₀) (rotatingAngle a₀) s
    change rotatingX a₀ s * _ + rotatingY a₀ s * _ = _ at x y
    rw [xs,ys] at x y
    exact (mark s ks (by change rotatingP a₀ s=0; simpa using x.symm)
      (by change rotatingQ a₀ s=0; simpa using y.symm)).2
  · rintro hs ⟨a,d,j,c,r⟩
    let z := periodicRotatingSupport ht hm hd
    have h := z.cubic_support_at_simple_inflection r kb
      (by change rotatingV a₀ 0≠0; rw [vb]; exact hb.ne')
    exact hs (by simpa only [show z.v 0=b from vb] using h.2.2.2.2)

end ClosedSimilarity.ReflectedArc
