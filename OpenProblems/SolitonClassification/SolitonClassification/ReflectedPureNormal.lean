import SolitonClassification.ReflectedShooting
import SolitonClassification.Rotating.RotatingNormalEvolution

/-! Closed pure-normal evolutions of the actual reflected shooting profiles. -/
noncomputable section
namespace ClosedSimilarity.ReflectedArc
open Set SolitonClassification.Rotating
open SolitonClassification.Rotating.NormalEvolution
set_option backward.isDefEq.respectTransparency false

private abbrev Six := SolitonClassification.Rotating.State

private def center6 (z : Six) : Six := ![-z 0,z 1,-z 2,-z 3,z 4,z 5]
private def axis6 (θ : ℝ) (z : Six) : Six := ![z 0,-z 1,z 2,-z 3,-z 4,2*θ-z 5]

private theorem clip_odd (r x : ℝ) (hr : 0 ≤ r) :
    clipScalar r (-x) = -clipScalar r x := by
  unfold clipScalar
  simp only [min_def,max_def]
  split_ifs <;> linarith

private theorem center_clip (z : Six) : clipState (center6 z)=center6 (clipState z) := by
  ext i
  fin_cases i <;> simp [center6,clipState,clippingRadius] <;> apply clip_odd <;> norm_num

private theorem axis_clip (θ : ℝ) (z : Six) : clipState (axis6 θ z)=axis6 θ (clipState z) := by
  ext i
  fin_cases i <;> simp [axis6,clipState,clippingRadius] <;> apply clip_odd <;> norm_num

private theorem center_field (z : Six) : clippedField (center6 z)= -center6 (clippedField z) := by
  unfold clippedField
  rw [center_clip]
  ext i
  fin_cases i <;> simp [center6,SolitonClassification.Rotating.field]
  ring

private theorem axis_field (θ : ℝ) (z : Six) :
    clippedField (axis6 θ z)= -axis6 0 (clippedField z) := by
  unfold clippedField
  rw [axis_clip]
  ext i
  fin_cases i <;> simp [axis6,SolitonClassification.Rotating.field]

private theorem reflect_deriv (a : Six) (c s : ℝ) :
    HasDerivAt (fun t => rotatingTrajectory a (c-t))
      (-(clippedField (rotatingTrajectory a (c-s)))) s := by
  have h : HasDerivAt (fun t : ℝ => c-t) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub c
  simpa only [Function.comp_def,neg_one_smul] using
    (rotatingTrajectory_derivative a (c-s)).scomp s h

private theorem center_deriv (a : Six) (c s : ℝ) :
    HasDerivAt (fun t => center6 (rotatingTrajectory a (c-t)))
      (clippedField (center6 (rotatingTrajectory a (c-s)))) s := by
  have h := hasDerivAt_pi.mp (reflect_deriv a c s)
  rw [center_field]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [center6,Pi.neg_def] using (h 0).neg
  · simpa [center6] using h 1
  · simpa [center6,Pi.neg_def] using (h 2).neg
  · simpa [center6,Pi.neg_def] using (h 3).neg
  · simpa [center6] using h 4
  · simpa [center6] using h 5

private theorem axis_deriv (a : Six) (c θ s : ℝ) :
    HasDerivAt (fun t => axis6 θ (rotatingTrajectory a (c-t)))
      (clippedField (axis6 θ (rotatingTrajectory a (c-s)))) s := by
  have h := hasDerivAt_pi.mp (reflect_deriv a c s)
  rw [axis_field]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [axis6] using h 0
  · simpa [axis6,Pi.neg_def] using (h 1).neg
  · simpa [axis6] using h 2
  · simpa [axis6,Pi.neg_def] using (h 3).neg
  · simpa [axis6,Pi.neg_def] using (h 4).neg
  · simpa [axis6] using (h 5).const_sub (2*θ)

private theorem reflected_at {a : Six} {c : ℝ} {r : Six → Six}
    (fixed : r (rotatingTrajectory a c)=rotatingTrajectory a c)
    (dr : ∀ s, HasDerivAt (fun t => r (rotatingTrajectory a (c-t)))
      (clippedField (r (rotatingTrajectory a (c-s)))) s) :
    ∀ s, rotatingTrajectory a (s+c)=r (rotatingTrajectory a (c-s)) := by
  have f := supportFlow_unique 1 (by norm_num)
    (x:=fun t => rotatingTrajectory a (t+c)) (a:=rotatingTrajectory a c)
    (by simp) (fun t => by simpa only [signedClippedField,one_smul] using
      rotatingTrajectory_shift_derivative a c t)
  have g := supportFlow_unique 1 (by norm_num)
    (x:=fun t => r (rotatingTrajectory a (c-t))) (a:=rotatingTrajectory a c)
    (by simpa using fixed) (fun t => by simpa only [signedClippedField,one_smul] using dr t)
  exact fun s => congrFun (f.trans g.symm) s

theorem reflected_endpoint_and_tube {b T : ℝ}
    (tube : ∀ s∈Icc 0 T, rotatingTrajectory (shootingStart b) s∈outerTube)
    (hv : rotatingTrajectory (shootingStart b) T 1=0)
    (hq : rotatingTrajectory (shootingStart b) T 3=0) :
    rotatingTrajectory (shootingStart b) (2*T)=
      rotatingTrajectory (shootingStart b) (-(2*T))+angleVector 0 ∧
    ∀ s∈Icc (-(2*T)) (2*T),rotatingTrajectory (shootingStart b) s∈outerTube := by
  let a := shootingStart b
  let x := rotatingTrajectory a
  let θ := x T 5
  have z0 : x 0=a := rotatingTrajectory_zero a
  have w0 : x T 4=0 := rotatingTrajectory_parameter_constant a T
  have f0 : center6 (x 0)=x 0 := by rw [z0]; ext i; fin_cases i <;> simp [a,shootingStart,center6]
  have f1 : axis6 θ (x T)=x T := by
    change x T 1=0 at hv
    change x T 3=0 at hq
    ext i
    fin_cases i <;> simp [axis6,θ,hv,hq,w0]
    ring
  have c (s : ℝ) : x s=center6 (x (-s)) := by
    simpa using reflected_at f0 (center_deriv a 0) s
  have e := reflected_at f1 (axis_deriv a T θ)
  have x2 : x (2*T)=axis6 θ a := by simpa [x,two_mul,rotatingTrajectory_zero] using e T
  have same : x (-(2*T))=x (2*T) := by
    rw [c (-(2*T)),neg_neg,x2]
    ext i
    fin_cases i <;> simp [center6,axis6,a,shootingStart]
  constructor
  · change x (2*T)=x (-(2*T))+angleVector 0
    rw [same]
    ext i
    simp [angleVector]
  · have pos (s : ℝ) (hs : s ∈ Icc 0 (2*T)) : x s∈outerTube := by
      by_cases h : s≤T
      · exact tube s ⟨hs.1,h⟩
      · have et : x s=axis6 θ (x (2*T-s)) := by
          simpa only [show s-T+T=s by ring,show T-(s-T)=2*T-s by ring] using e (s-T)
        rw [et]
        simpa [outerTube,axis6] using tube (2*T-s) ⟨by linarith [hs.2],by linarith⟩
    intro s hs
    by_cases h : 0≤s
    · exact pos s ⟨h,hs.2⟩
    · change x s∈outerTube
      rw [c s]
      simpa [outerTube,center6] using pos (-s) ⟨by linarith,by linarith [hs.1]⟩

/-- The period, zero total curvature, initial profile and length evolution all
refer to the actual interpolated shooting trajectory. -/
theorem reflected_shooting_exists_pure_normal_evolution {b T : ℝ} (hT : 0<T)
    (tube : ∀ s∈Icc 0 T, rotatingTrajectory (shootingStart b) s∈outerTube)
    (hv : rotatingTrajectory (shootingStart b) T 1=0)
    (hq : rotatingTrajectory (shootingStart b) T 3=0) :
    (∫s in 0..(4*T),rotatingK (shootingStart b) s)=0 ∧
    ∃ X Y : ℝ → ℝ → ℝ, IsPureNormalElasticEvolution (4*T) X Y ∧
      (∀s,X 0 s=rotatingX (shootingStart b) s ∧ Y 0 s=rotatingY (shootingStart b) s) ∧
      (∀t,(∫s in 0..(4*T),curveSpeed (X t) (Y t) s)=dilationScale t*(4*T)) := by
  obtain ⟨hm,ht⟩ := reflected_endpoint_and_tube tube hv hq
  have ht' : 0<2*T := by linarith
  have hL : ((1:ℕ):ℝ)*(2*(2*T))=4*T := by push_cast; ring
  have hol : ((1:ℕ):ℝ)*0=((0:ℤ):ℝ)*(2*Real.pi) := by norm_num
  have hp := closed_rotating_profile_of_endpoint ht' hm ht 1 (by decide) 0 hol
  have hk := rotating_total_curvature ht' hm ht 1 0 hol
  rw [hL] at hp hk
  refine ⟨by simpa using hk,normalX _ _ hp,normalY _ _ hp,
    normalEvolution_is_pure_normal _ _ hp,?_,normal_length _ _ hp⟩
  exact fun s => ⟨normalX_initial _ _ hp s,normalY_initial _ _ hp s⟩

#print axioms reflected_shooting_exists_pure_normal_evolution
end ClosedSimilarity.ReflectedArc
