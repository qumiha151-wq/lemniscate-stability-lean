import SolitonClassification.Rotating.IntegerHullReconstruction
import SolitonClassification.Rotating.ResetHullSamples
import SolitonClassification.Rotating.IntegerTurningPeriod

namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
open Set Metric
open scoped ContDiff
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

private theorem hull_cube_parameters {c : Parameters} (hc : c∈cube) :
    30<c 2 ∧ c 2<31 ∧ 1/10<c 4 ∧ c 4<11/100 ∧ 7<c 0 ∧ 0<c 3 := by
  have hn : ‖c-center‖≤1/(10:ℝ)^30 := hc
  have he (i : Fin 5) : |c i-(centerQ i:ℝ)|≤1/(10:ℝ)^30 :=
    (norm_le_pi_norm (c-center) i).trans hn
  have limits (i : Fin 5) (l u : ℚ)
      (h₁ : l+1/10^30<centerQ i) (h₂ : centerQ i<u-1/10^30) :
      (l:ℝ)<c i ∧ c i<(u:ℝ) := by
    have a := (Rat.cast_lt (K:=ℝ)).mpr h₁
    have b := (Rat.cast_lt (K:=ℝ)).mpr h₂
    push_cast at a b
    have v := abs_le.mp (he i)
    constructor <;> linarith [v.1,v.2]
  have tt := limits 2 30 31 (by decide +kernel) (by decide +kernel)
  have bb := limits 4 (1/10) (11/100) (by decide +kernel) (by decide +kernel)
  have kk := limits 0 7 8 (by decide +kernel) (by decide +kernel)
  have aa := limits 3 0 1 (by decide +kernel) (by decide +kernel)
  push_cast at tt bb kk aa
  exact ⟨tt.1,tt.2,bb.1,bb.2,kk.1,aa.1⟩

/-- Given the physical two-arm enclosure and the original initial value
problem on each candidate segment, the contraction produces a genuine closed
unit-speed plane immersion. Its local curvature exceeds seven, its signed
angle increment is negative, and its rotation term is nonzero at the origin
of the arclength parametrization. -/
theorem immersion_with_square_of_shooting_bounds
    (Φ : ℝ×State → State) (DΦ : ℝ×State → (ℝ×State) →L[ℝ] State)
    (hp : ArmBounds Φ DΦ (forwardEndpointInput phase) plusQ plusColumn)
    (hm : ArmBounds Φ DΦ (backwardEndpointInput phase) minusQ minusColumn)
    (actual : ∀c∈cube,∀s∈Icc lowerTime upperTime, framePosition (Φ (s,shootingInitial phase c))=segmentPosition c s)
    (initial : ∀c∈cube, Φ (0,shootingInitial phase c)=shootingInitial phase c)
    (ode : ∀c∈cube, ∀s∈Icc (-(c 2)) (c 2), HasDerivAt
      (fun u => Φ (u,shootingInitial phase c)) (field (Φ (s,shootingInitial phase c))) s) :
    ∃ c∈cube, ∃ I : WindingOneImmersion (c 4) (2*c 2),
      60<2*c 2 ∧ 2*c 2<62 ∧ 1/10<c 4 ∧ c 4<11/100 ∧ 7<I.k 0 ∧
      (∃s, I.k s<0) ∧ c 4*(I.x 0*deriv I.x 0+I.y 0*deriv I.y 0)≠0 ∧
      IsLeast {h : ℝ | 0<h ∧ Function.Periodic I.x h ∧ Function.Periodic I.y h} (2*c 2) ∧
      (∀w : ℝ × ℝ, |w.1|≤1/20 → |w.2|≤1/20 → w∈convexHull ℝ (Set.range (fun s => (I.x s,I.y s)))) := by
  obtain ⟨c,hc,zero,_⟩ := unique_root_of_arm_bounds Φ DΦ hp hm
  obtain ⟨T0,T1,b0,b1,k0,u0⟩ := hull_cube_parameters hc
  let T := c 2
  have hT : 0<T := by dsimp [T]; linarith
  let z := fun s : ℝ => Φ (s,shootingInitial phase c)
  have ini : z 0=shootingInitial phase c := initial c hc
  have iv (i : Fin 6) := congrFun (ini.trans (shootingInitial_apply phase c)) i
  have ib : z 0 4=c 4 := iv 4
  have ik : z 0 0=c 0 := iv 0
  have iq : z 0 3=c 3*phase 1 := iv 3
  have dz (s : ℝ) (hs : s∈Icc (-T) T) : HasDerivAt z (field (z s)) s :=
    ode c hc s hs
  have bp : z T 4=z (-T) 4 := by
    have hd (s : ℝ) (hs : s∈Icc (-T) T) : HasDerivAt (fun u => z u 4) 0 s :=
      (ContinuousLinearMap.proj (4:Fin 6) : State→L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s (dz s hs)
    have eq := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f:=fun s => z s 4) (f':=fun _ => (0:ℝ)) (a:= -T) (b:=T)
      (fun x hx => hd x (by simpa [uIcc_of_le (by linarith : -T≤T)] using hx))
      (intervalIntegrable_const)
    exact sub_eq_zero.mp (by simpa using eq.symm)
  have rh := (residual_zero_iff Φ c).mp zero
  change z T 0=z (-T) 0 ∧ z T 1=z (-T) 1 ∧ z T 2=z (-T) 2 ∧
    z T 3=z (-T) 3 ∧ z T 5-z (-T) 5= -2*Real.pi at rh
  obtain ⟨h0,h1,h2,h3,h5⟩ := rh
  have matched : z T=z (-T)+angleVector (-2*Real.pi) := by
    ext i
    fin_cases i <;> simp [angleVector,h0,h1,h2,h3,bp]
    linarith
  have pack := immersion_with_arc_coordinates hT z dz matched
  rw [ib] at pack
  obtain ⟨I,ki,qi,arc⟩ := pack
  have negative : ∃s, I.k s<0 := by
    by_contra! hn
    have mono : Monotone I.theta := monotone_of_deriv_nonneg
      (fun s => (I.angleDerivative s).differentiableAt)
      (fun s => by rw [(I.angleDerivative s).deriv]; exact hn s)
    have m := mono (show 0≤0+2*T by linarith)
    rw [I.turning] at m
    linarith [Real.pi_pos]
  have sign : phase 1<0 := by norm_num [phase,phaseQ]
  refine ⟨c,hc,I,by linarith,by linarith,b0,b1,by rwa [ki,ik],negative,?_,I.least_positive_period (by linarith),?_⟩
  · rw [qi,iq]
    exact mul_ne_zero (by linarith) (mul_ne_zero (ne_of_gt u0) (ne_of_lt sign))
  · intro w wx wy
    apply convexHull_mono _ (square_in_shooting_arc hc w wx wy)
    rintro point ⟨s,hs,rfl⟩
    have hseg : s∈Icc (-T) T := ⟨by dsimp [T]; linarith [hs.1,sample_times.2.2.1],by dsimp [T]; linarith [hs.2,sample_times.2.2.2]⟩
    exact ⟨s,(arc s hseg).trans (actual c hc s hs)⟩
end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.immersion_with_square_of_shooting_bounds
