import SolitonClassification.MeromorphicDifferenceJet

noncomputable section
open Complex Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace ClosedSimilarity.MeromorphicCurvature
open RationalCurvature

/-- Two distinct solutions with the same residue at an admissible pole can first
differ at only the fifth regular power. -/
theorem pole_difference_order_five {f g : ℂ → ℂ} {x a b c d : ℂ} {m : ℤ}
    (hf : Jet f x (-1) c) (hg : Jet g x (-1) c) (hc : c^2 = -9)
    (hd : Jet (fun z=>f z-g z) x m d) (dn : d≠0) (hm : 0≤m)
    (rf : ordinaryResidual a b f =ᶠ[𝓝[≠] x] fun _=>0)
    (rg : ordinaryResidual a b g =ᶠ[𝓝[≠] x] fun _=>0) : m=5 := by
  let t := (m:ℂ)
  have j : DifferenceJet x (m+1) (-1) c d f g :=
    ⟨hf,hg,hd.retag (by omega) rfl⟩
  have j1 : DifferenceJet x (m+1) (-2) (-c) (t*d) (deriv f) (deriv g) := by
    apply j.deriv.retag <;> norm_num [t]
  have j2 : DifferenceJet x (m+1) (-3) (2*c) ((t-1)*t*d)
      (deriv (deriv f)) (deriv (deriv g)) := by
    apply j1.deriv.retag <;> norm_num [t]
    all_goals ring
  have j3 : DifferenceJet x (m+1) (-4) (-6*c) ((t-2)*(t-1)*t*d)
      (deriv (deriv (deriv f))) (deriv (deriv (deriv g))) := by
    apply j2.deriv.retag <;> norm_num [t]
    all_goals ring
  have j4 : DifferenceJet x (m+1) (-5) (24*c) ((t-3)*(t-2)*(t-1)*t*d)
      (deriv (deriv (deriv (deriv f)))) (deriv (deriv (deriv (deriv g)))) := by
    apply j3.deriv.retag <;> norm_num [t]
    all_goals ring
  have quadratic := (((j.mul j4).retag (N:=-6) (by norm_num) rfl rfl).sub
    ((j1.mul j3).retag (N:=-6) (by norm_num) rfl rfl)).smul 2
  have quartic := ((((j.pow 2).mul (j1.pow 2)).retag (N:=-6) (by norm_num) rfl rfl).smul 3).add
    ((((j.pow 3).mul j2).retag (N:=-6) (by norm_num) rfl rfl).smul 5)
  have higher := ((j.pow 6).retag (N:=-6) (by norm_num) rfl rfl)
  have lowerA := (((j.pow 2).smul (2*a)).weaken (m:=-6) (by norm_num))
  have lowerB := ((j1.smul (2*b)).weaken (m:=-6) (by norm_num))
  have body := ((((quadratic.add quartic).add higher).sub lowerA).sub lowerB).change
  have zero := body.eq_zero_of_germ_zero (show (fun z=>ordinaryResidual a b f z -
      ordinaryResidual a b g z)=ᶠ[𝓝[≠] x] fun _=>0 from by
    filter_upwards [rf,rg] with z u v
    simp [u,v])
  norm_num at zero
  have eq : c*d*(t+2)*(t-5)*(2*t^2-4*t-21)=0 := by
    linear_combination zero-(c*d*(5*t^2-11*t-18+6*c^2))*hc
  have cn : c≠0 := by intro z; simp [z] at hc
  have hplus : t+2≠0 := by
    intro v
    dsimp [t] at v
    have vv : (m+2:ℤ)=0 := by exact_mod_cast v
    omega
  rcases mul_eq_zero.mp eq with v|v
  · have zz := (mul_eq_zero.mp v).resolve_left (mul_ne_zero (mul_ne_zero cn dn) hplus)
    have me : (m:ℂ)=5 := sub_eq_zero.mp zz
    exact_mod_cast me
  · dsimp [t] at v
    have parity : (2*m^2-4*m-21 : ℤ)=0 := by exact_mod_cast v
    omega

end ClosedSimilarity.MeromorphicCurvature
#print axioms ClosedSimilarity.MeromorphicCurvature.pole_difference_order_five
