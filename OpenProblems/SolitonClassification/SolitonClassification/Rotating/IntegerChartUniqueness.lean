import SolitonClassification.Rotating.IntegerChartIntersection

namespace SolitonClassification.Rotating.IntegerTarget.CrossingCharts
noncomputable section
open Set

private theorem directional_rolle {c : Parameters} (hc : c∈cube) {k : Fin 2} {arm : Bool}
    {a b : ℝ} (ha : a∈dom k arm) (hb : b∈dom k arm) (ne : a≠b) (A B : ℝ)
    (ends : A*(gridPosition c a).1+B*(gridPosition c a).2=
            A*(gridPosition c b).1+B*(gridPosition c b).2) :
    ∃s∈dom k arm, A*Real.cos (gridAngle c s)+B*Real.sin (gridAngle c s)=0 := by
  let f := fun u => A*(gridPosition c u).1+B*(gridPosition c u).2
  let D := fun u => (A*Real.cos (gridAngle c u)+B*Real.sin (gridAngle c u))*h
  have rates (u) (hu : u∈dom k arm) : HasDerivAt f (D u) u := by
    obtain ⟨dx,dy,_⟩ := grid_rates hc u (dom_grid hu)
    convert (dx.const_mul A).add (dy.const_mul B) using 1 <;> try rfl
    all_goals ring
  have seek {x y : ℝ} (hx : x∈dom k arm) (hy : y∈dom k arm) (lt : x<y) (eqn : f x=f y) :
      ∃s∈dom k arm, A*Real.cos (gridAngle c s)+B*Real.sin (gridAngle c s)=0 := by
    have inside : Icc x y ⊆ dom k arm := Icc_subset_Icc hx.1 hy.2
    have cont : ContinuousOn f (Icc x y) := fun u hu => (rates u (inside hu)).continuousAt.continuousWithinAt
    obtain ⟨s,hs,zero⟩ := exists_hasDerivAt_eq_zero lt cont eqn (fun u hu => rates u (inside (Ioo_subset_Icc_self hu)))
    exact ⟨s,inside (Ioo_subset_Icc_self hs),(mul_eq_zero.mp zero).resolve_right h_mem.1.ne'⟩
  rcases lt_or_gt_of_ne ne with lt | gt
  · exact seek ha hb lt ends
  · exact seek hb ha gt ends.symm

/-- Two disjoint smooth arcs with independent tangents at every pair of
parameters cross at most once inside their parameter rectangle. -/
theorem unique_chart_parameters {c : Parameters} (hc : c∈cube) {k : Fin 2}
    (transverse : ∀s∈dom k false,∀t∈dom k true, Real.sin (gridAngle c t-gridAngle c s)≠0)
    {a b a' b' : ℝ} (ha : a∈dom k false) (hb : b∈dom k true)
    (ha' : a'∈dom k false) (hb' : b'∈dom k true)
    (cross₁ : gridPosition c a=gridPosition c b) (cross₂ : gridPosition c a'=gridPosition c b') :
    a=a' ∧ b=b' := by
  let X := gridPosition c
  let dx := (X b').1-(X b).1
  let dy := (X b').2-(X b).2
  have first : ∃s∈dom k false, dy*Real.cos (gridAngle c s)-dx*Real.sin (gridAngle c s)=0 := by
    by_cases e : a=a'
    · have same := cross₁.symm.trans ((congrArg (gridPosition c) e).trans cross₂)
      refine ⟨a,ha,?_⟩
      simp [dx,dy,X,same]
    · have ends : dy*(X a).1+(-dx)*(X a).2=dy*(X a').1+(-dx)*(X a').2 := by
        change dy*(gridPosition c a).1+(-dx)*(gridPosition c a).2=dy*(gridPosition c a').1+(-dx)*(gridPosition c a').2
        rw [cross₁,cross₂]
        dsimp [dx,dy,X]
        ring
      obtain ⟨s,hs,q⟩ := directional_rolle hc ha ha' e dy (-dx) ends
      exact ⟨s,hs,by linarith⟩
  have eb : b=b' := by
    by_contra ne
    obtain ⟨s,hs,perp⟩ := first
    have ends : (-Real.sin (gridAngle c s))*(X b).1+Real.cos (gridAngle c s)*(X b).2=
        (-Real.sin (gridAngle c s))*(X b').1+Real.cos (gridAngle c s)*(X b').2 := by
      dsimp only [dx,dy] at perp
      linarith only [perp]
    obtain ⟨t,ht,eqn⟩ := directional_rolle hc hb hb' ne _ _ ends
    apply transverse s hs t ht
    rw [Real.sin_sub]
    linear_combination eqn
  refine ⟨?_,eb⟩
  by_contra ne
  have same := cross₁.trans ((congrArg (gridPosition c) eb).trans cross₂.symm)
  let A := Real.sin (gridAngle c b)
  let B := -Real.cos (gridAngle c b)
  have ends : A*(gridPosition c a).1+B*(gridPosition c a).2=
      A*(gridPosition c a').1+B*(gridPosition c a').2 := by rw [same]
  obtain ⟨s,hs,eqn⟩ := directional_rolle hc ha ha' ne A B ends
  apply transverse s hs b hb
  rw [Real.sin_sub]
  dsimp only [A,B] at eqn
  linear_combination eqn

end
end SolitonClassification.Rotating.IntegerTarget.CrossingCharts
#print axioms SolitonClassification.Rotating.IntegerTarget.CrossingCharts.unique_chart_parameters

