import SolitonClassification.ReflectedPhysicalMarker
import SolitonClassification.Reflected.NumericInput

/-! Geometric conclusion for the explicit positive-slope shooting rectangle. -/
noncomputable section
namespace ClosedSimilarity.ReflectedArc
open Set SolitonClassification.Rotating
open SolitonClassification.Rotating.NormalEvolution
open SolitonClassification.Reflected (slopes times shot velocity tangentSupport)
set_option backward.isDefEq.respectTransparency false

/-- The curvature, centre crossing, zero total turning and genuine normal
evolution all refer to the same initial curve. -/
structure FirstProfile (b T : ℝ) : Prop where
  slope_bounds : 719/1000 < b ∧ b < 720/1000
  quarter_bounds : 57/10 < T ∧ T < 571/100
  total_turn : (∫s in 0..(4*T),rotatingK (shootingStart b) s)=0
  center : rotatingX (shootingStart b) 0=0 ∧ rotatingY (shootingStart b) 0=0 ∧
    rotatingK (shootingStart b) 0=0 ∧ deriv (rotatingK (shootingStart b)) 0=b
  marker : ∀ s, rotatingK (shootingStart b) s=0 → rotatingX (shootingStart b) s=0 →
    rotatingY (shootingStart b) s=0 → |deriv (rotatingK (shootingStart b)) s|=b
  noncubic : ¬∃ a d j c : ℝ, ∀ s, rotatingP (shootingStart b) s =
    a*(rotatingK (shootingStart b) s)^3 + d*(rotatingK (shootingStart b) s)^2 +
    j*rotatingK (shootingStart b) s+c
  evolution : ∃ X Y : ℝ → ℝ → ℝ, IsPureNormalElasticEvolution (4*T) X Y ∧
    (∀s,X 0 s=rotatingX (shootingStart b) s ∧ Y 0 s=rotatingY (shootingStart b) s) ∧
    (∀t,(∫s in 0..(4*T),curveSpeed (X t) (Y t) s)=dilationScale t*(4*T))

theorem firstProfile_of_zero {b T : ℝ} (hb : b∈slopes) (ht : T∈times)
    (hv : velocity (b,T)=0) (hq : tangentSupport (b,T)=0)
    (tube : ∀ s∈Icc 0 T, shot b s∈outerTube) : FirstProfile b T := by
  have hbl := hb.1
  have hbu := hb.2
  have htl := ht.1
  have htu := ht.2
  norm_num [SolitonClassification.Reflected.leftSlope,SolitonClassification.Reflected.rightSlope,
    SolitonClassification.Reflected.center,SolitonClassification.Reflected.width] at hbl hbu htl htu
  have bs : 719/1000<b ∧ b<720/1000 := ⟨by linarith,by linarith⟩
  have ts : 57/10<T ∧ T<571/100 := ⟨by linarith,by linarith⟩
  have hT : 0<T := by linarith [ts.1]
  have bpos : 0<b := by linarith [bs.1]
  have vn : rotatingTrajectory (shootingStart b) T 1=0 :=
    (mul_eq_zero.mp hv).resolve_left (by norm_num)
  obtain ⟨ax,ay,k,dk,mark,nc⟩ := shooting_profile_marker hT bpos tube vn hq
  obtain ⟨turn,evol⟩ := reflected_shooting_exists_pure_normal_evolution hT tube vn hq
  have neq : b^2 ≠ 6/5 := by nlinarith [sq_lt_sq' (show -(1:ℝ)<b by linarith) (show b<1 by linarith [bs.2])]
  exact ⟨bs,ts,turn,⟨ax,ay,k,dk⟩,mark,nc neq,evol⟩

end ClosedSimilarity.ReflectedArc
