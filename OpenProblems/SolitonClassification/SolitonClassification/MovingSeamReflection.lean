import SolitonClassification.MovingSeamSlab

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open FrozenStress

def reverse (x : Phase) : Phase := ![x 0,-x 1,x 2,-x 3]

theorem reverse_involutive (x : Phase) : reverse (reverse x) = x := by
  ext i; fin_cases i <;> simp [reverse]

/-- The arclength reversor is exact at every seam scale. -/
theorem shot_reflection (d c t : ℝ) : shot d c (-t) = reverse (shot d c t) := by
  let f := shot d c
  let X := fun s : ℝ => reverse (f (-s))
  have init : X 0 = ![c,0,1,0] := by simp [X,f,shot,solution_zero,reverse]
  have dx (s : ℝ) : HasDerivAt X (rhs d (X s)) s := by
    have hn : HasDerivAt (fun r : ℝ => -r) (-1) s := by
      simpa [Pi.neg_def,id_def] using (hasDerivAt_id s).neg
    have h := hasDerivAt_pi.mp (solution_derivative d ![c,0,1,0] (-s))
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [X,f,shot,rhs,reverse,Function.comp_def] using (h 0).comp s hn
    · simpa [X,f,shot,rhs,reverse,Function.comp_def,Pi.neg_def] using ((h 1).comp s hn).neg
    · simpa [X,f,shot,rhs,reverse,Function.comp_def] using (h 2).comp s hn
    · simpa [X,f,shot,rhs,reverse,Function.comp_def,Pi.neg_def] using ((h 3).comp s hn).neg
  have same := (exists_unique_solution d ![c,0,1,0]).unique
    ⟨init,dx⟩ ⟨solution_zero _ _,solution_derivative _ _⟩
  have h := congrArg reverse (congrFun same t)
  change reverse (reverse (shot d c (-t))) = reverse (shot d c t) at h
  rwa [reverse_involutive] at h

def impact (z : Phase) := (root z/scale z)*across z

theorem impact_continuousAt {z : Phase} (h : regular z) : ContinuousAt impact z := by
  have sp : 0 < scale z := Real.rpow_pos_of_pos h.1 _
  have ap : 0 < amplitude z := Real.sqrt_pos.mpr h.2
  have cs : ContDiffAt ℝ 1 scale z := by
    apply ContDiffAt.rpow_const_of_ne _ h.1.ne'
    unfold radiusSquared; fun_prop
  have ca : ContDiffAt ℝ 1 amplitude z := by
    apply ContDiffAt.sqrt _ h.2.ne'
    unfold stressSquared; fun_prop
  have cr : ContDiffAt ℝ 1 root z := ca.sqrt ap.ne'
  have cb : ContDiffAt ℝ 1 across z := by
    apply ContDiffAt.div _ (ca.mul (cs.pow 3)) (by positivity); fun_prop
  exact ((cr.div cs sp.ne').mul cb).continuousAt

theorem frozen_impact (c t : ℝ) : impact (shot 0 c t) = seamImpact c t := by
  rw [shot_frozen]
  let z := seam c
  have hs : scale (coords z t)=1 := by simp [scale,radiusSquared,coords,z.unit t]
  change impact (coords z t)=z.root t*z.across t
  simp only [impact,across,hs,one_pow,mul_one,div_one]
  rfl

theorem reflected_data (x : Phase) :
    height (reverse x) = -height x ∧ impact (reverse x) = impact x ∧
    radiusSquared (reverse x)=radiusSquared x := by
  have rad : radiusSquared (reverse x) = radiusSquared x := by simp [radiusSquared,reverse]
  have a : amplitude (reverse x) = amplitude x := by simp [amplitude,stressSquared,reverse]
  have s : scale (reverse x) = scale x := by simp only [scale,rad]
  have r : root (reverse x) = root x := by simp only [root,a]
  have along' : along (reverse x) = -along x := by simp only [along,a,s]; simp [reverse]; ring
  have across' : across (reverse x) = across x := by simp only [across,a,s]; simp [reverse]
  have shape' : shape (reverse x) = shape x := by simp only [shape,r]; rfl
  have slope' : slope (reverse x) = -slope x := by simp only [slope,a]; simp [reverse,neg_div]
  refine ⟨?_,?_,rad⟩
  · simp only [height,r,s,along',across',shape',slope',chi]; ring
  · simp only [impact,r,s,across']

theorem negative_section (d c t H : ℝ) (h : height (shot d c t)=H) :
    -height (shot d c (-t)) = H ∧ impact (shot d c (-t)) = impact (shot d c t) ∧
      radiusSquared (shot d c (-t))=radiusSquared (shot d c t) := by
  rw [shot_reflection]
  obtain ⟨one,two,three⟩ := reflected_data (shot d c t)
  exact ⟨by rw [one,neg_neg,h],two,three⟩

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.negative_section
