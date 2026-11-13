module

public import SolitonClassification.Rotating.RotatingClosedProfileShooting

@[expose] public section

/-! Optional genuine-rotation conclusions from explicit initial bounds.
The inequalities k(0)>2 and b>0 are inputs for later candidate-box
certification, not facts asserted about an uninstantiated numeric root. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

theorem rotatingK_nonconstant_of_initial_bound {a : State} {T d : ℝ} (hT : 0<T)
    (hmatch : rotatingTrajectory a T=rotatingTrajectory a (-T)+angleVector d)
    (htube : ∀s∈Icc (-T) T,rotatingTrajectory a s∈outerTube) (hk0 : 2<a 0) :
    ¬∃k₀ : ℝ,∀s,rotatingK a s=k₀ := by
  rintro ⟨k₀,hk⟩
  have he : k₀=a 0 := by
    have h := hk 0
    simpa only [rotatingK,rotatingTrajectory_zero] using h.symm
  subst k₀
  let z := periodicRotatingSupport hT hmatch htube
  have hc : a 0≠0 := by linarith
  have hfour := (z.constant_curvature_support (by norm_num : 0<(1:ℝ)) hc hk).1
  have hsq : 4<(a 0)^2 := by nlinarith
  have hpow : 16<(a 0)^4 := by nlinarith [sq_nonneg ((a 0)^2-4)]
  norm_num at hfour
  linarith

theorem rotating_tangent_support_nonzero {a : State}
    (htube : ∀s,rotatingTrajectory a s∈outerTube)
    (hnot : ¬∃k₀ : ℝ,∀s,rotatingK a s=k₀) : ∃s,rotatingQ a s≠0 := by
  by_contra hnone
  push Not at hnone
  have hqfun : rotatingQ a=fun _ => 0 := funext hnone
  have hpd (s : ℝ) : HasDerivAt (rotatingP a) 0 s := by
    simpa only [hnone s,mul_zero,neg_zero] using rotatingP_derivative htube s
  have hp (s : ℝ) : rotatingP a s=rotatingP a 0 :=
    is_const_of_deriv_eq_zero (fun t => (hpd t).differentiableAt) (fun t => (hpd t).deriv) s 0
  have hq (s : ℝ) : 1+rotatingK a s*rotatingP a s=0 := by
    have hd : HasDerivAt (rotatingQ a) 0 s := by rw [hqfun]; exact hasDerivAt_const s 0
    exact (rotatingQ_derivative htube s).unique hd
  have hp0 : rotatingP a 0≠0 := by
    intro hz
    have h := hq 0
    rw [hz,mul_zero,add_zero] at h
    norm_num at h
  apply hnot
  refine ⟨-1/rotatingP a 0,fun s => ?_⟩
  apply (eq_div_iff hp0).mpr
  have h := hq s
  rw [hp s] at h
  linarith

theorem rotating_normal_rotation_term_nonzero {a : State}
    (htube : ∀s,rotatingTrajectory a s∈outerTube)
    (hnot : ¬∃k₀ : ℝ,∀s,rotatingK a s=k₀) (hb : a 4≠0) :
    ∃s,a 4*(rotatingX a s*deriv (rotatingX a) s+rotatingY a s*deriv (rotatingY a) s)≠0 := by
  obtain ⟨s,hs⟩ := rotating_tangent_support_nonzero htube hnot
  refine ⟨s,?_⟩
  obtain ⟨hx,hy⟩ := rotating_position_derivatives htube s
  rw [hx.deriv,hy.deriv]
  change a 4*(ClosedSimilarity.profileX (rotatingP a) (rotatingQ a) (rotatingAngle a) s*
    Real.cos (rotatingAngle a s)+ClosedSimilarity.profileY (rotatingP a) (rotatingQ a) (rotatingAngle a) s*
    Real.sin (rotatingAngle a s))≠0
  rw [ClosedSimilarity.tangent_support]
  exact mul_ne_zero hb hs

theorem actualShooting_nonconstant_rotating (e : Fin 2 → ℝ) (c : Parameters)
    (hT : 0<c 2) (hzero : actualShootingMap e c=0)
    (htube : ∀s∈Icc (-c 2) (c 2),rotatingTrajectory (shootingInitial e c) s∈outerTube)
    (hk0 : 2<c 0) (hb : 0<c 4) :
    (¬∃k₀ : ℝ,∀s,rotatingK (shootingInitial e c) s=k₀) ∧
    ∃s,c 4*(rotatingX (shootingInitial e c) s*deriv (rotatingX (shootingInitial e c)) s+
      rotatingY (shootingInitial e c) s*deriv (rotatingY (shootingInitial e c)) s)≠0 := by
  have hm := actualShooting_endpoint_match e c hzero
  have hkinit : 2<shootingInitial e c 0 := by simpa [shootingInitial_apply] using hk0
  have hbinit : shootingInitial e c 4≠0 := by simpa [shootingInitial_apply] using hb.ne'
  have hn := rotatingK_nonconstant_of_initial_bound hT hm htube hkinit
  refine ⟨hn,?_⟩
  simpa [shootingInitial_apply] using rotating_normal_rotation_term_nonzero
    (rotatingTrajectory_global_tube hT hm htube) hn hbinit

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name || (`ClosedSimilarity).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating nonconstant actual-profile audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating nonconstant actual-profile audit passed for {count} declarations."
