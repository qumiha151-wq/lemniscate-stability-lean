import LengthGrowth.ActualFlow.InflectionQuarterFlow
import LengthGrowth.ActualFlow.InflectionRootSigns
import LengthGrowth.ActualFlow.InflectionVelocitySeparation
import LengthGrowth.ActualFlow.IntegrableTurningBudget

noncomputable section
open Set MeasureTheory
namespace LengthGrowth.ActualFlow.ForwardImmersion

/-- A continuous integrable upper bound on the pairwise outward force
    derivative at curvature zeros gives fourth-root growth for this
    genuine solution. Degenerate and absent inflections are allowed. -/
theorem quarter_length_of_integrable_outward_inflection_bound (c : ForwardImmersion)
    (flow : c.IsNormalFEF) {T : ℝ} (r : ℝ→ℝ) (cr : Continuous r)
    (ir : IntegrableOn r (Ioi T)) (pos : ∀t>T,0≤r t)
    (bound : ∀t>T,∀ x y,curvature (c.position t) x=0 → curvatureGradient (c.position t) x≤0 →
      curvature (c.position t) y=0 → 0≤curvatureGradient (c.position t) y →
      arcDerivative (c.position t) (force (c.position t)) y-
        arcDerivative (c.position t) (force (c.position t)) x≤r t) : c.HasQuarterLengthBound := by
  obtain ⟨a,ap,ta,B,cb,db,small⟩ := TurningEnvelope.small_tail_budget cr ir
  let J := fun t => arcDerivative (c.position t) (force (c.position t))
  have separates (t : ℝ) (ht : a<t) : ∃ v : ℝ,
      (∀x,IsLocalMax (arcTurn (c.position t) 0) x → -J t x≤v+r t) ∧
      (∀y,IsLocalMin (arcTurn (c.position t) 0) y → v≤ -J t y) := by
    let p := c.regularPositionAt (ap.trans ht).le
    obtain ⟨v,up,down⟩ := p.separating_inflection_velocity (bound t (ta.trans ht))
    exact ⟨v,fun x hx=>let ⟨z,s⟩:=p.max_inflection_sign hx; up x z s,
              fun y hy=>let ⟨z,s⟩:=p.min_inflection_sign hy; down y z s⟩
  classical
  let ref := fun t => if ht : a<t then (separates t ht).choose else 0
  apply c.quarter_length_of_one_sided_inflection_budget flow ap B r ref cb.continuousOn (fun t _=>db t)
    (fun t ht=>pos t (ta.trans ht)) small
  · intro t ht x hx
    simpa only [ref,dif_pos ht] using (separates t ht).choose_spec.1 x hx
  · intro t ht y hy
    simpa only [ref,dif_pos ht] using (separates t ht).choose_spec.2 y hy

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_length_of_integrable_outward_inflection_bound
