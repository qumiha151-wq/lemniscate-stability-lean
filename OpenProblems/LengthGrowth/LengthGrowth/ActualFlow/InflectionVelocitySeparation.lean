import LengthGrowth.ActualFlow.MaterialTurnPrimitives
import LengthGrowth.ActualFlow.CyclicTurnVariation

noncomputable section
open Set Function
open scoped ContDiff
namespace LengthGrowth.ActualFlow.PeriodicRegularPosition

/-- Pairwise outward velocity control is equivalent to admitting a common
    separating value between the two types of inflection. Either type can be empty. -/
theorem separating_inflection_velocity (p : PeriodicRegularPosition) {r : ℝ}
    (pairs : ∀x y, curvature p.position x=0 → curvatureGradient p.position x≤0 →
        curvature p.position y=0 → 0≤curvatureGradient p.position y →
        arcDerivative p.position (force p.position) y-arcDerivative p.position (force p.position) x≤r) :
    ∃ v : ℝ, (∀x, curvature p.position x=0 → curvatureGradient p.position x≤0 →
      -arcDerivative p.position (force p.position) x≤v+r) ∧
      (∀y, curvature p.position y=0 → 0≤curvatureGradient p.position y →
        v≤ -arcDerivative p.position (force p.position) y) := by
  let F := arcDerivative p.position (force p.position)
  let V := fun u => -F u
  have s := force_smooth p.smooth p.regular
  have cv : Continuous V := (arcDerivative_smooth p.smooth p.regular s).continuous.neg
  have fp : Periodic F p.period := arcDerivative_periodic p.smooth p.periodic (s.differentiable (by simp))
    (force_periodic p.smooth p.regular p.periodic)
  have vp : Periodic V p.period := fun u => congrArg Neg.neg (fp u)
  have inImage (u : ℝ) : V u∈V '' Icc 0 p.period := by
    have eq := vp.sub_zsmul_eq (x:=u) (toIcoDiv p.period_pos 0 u)
    rw [self_sub_toIcoDiv_zsmul] at eq
    exact ⟨_,Ico_subset_Icc_self (toIcoMod_mem_Ico' p.period_pos u),eq⟩
  have kc : IsCompact (V '' Icc 0 p.period) := isCompact_Icc.image cv
  let M := {u | curvature p.position u=0 ∧ curvatureGradient p.position u≤0}
  by_cases ne : (V '' M).Nonempty
  · have bd : BddAbove (V '' M) := kc.bddAbove.mono (fun _ h=>by obtain ⟨u,_,rfl⟩:=h; exact inImage u)
    refine ⟨sSup (V '' M)-r,?_,?_⟩
    · intro x k g
      have root : x∈M := ⟨k,g⟩
      have bound := le_csSup bd (mem_image_of_mem V root)
      change V x≤sSup (V '' M)-r+r
      linarith
    · intro y ky gy
      change sSup (V '' M)-r≤V y
      apply sub_le_iff_le_add.mpr
      apply csSup_le ne
      rintro _ ⟨x,hx,rfl⟩
      change -F x≤ -F y+r
      have h := pairs x y hx.1 hx.2 ky gy
      change F y-F x≤r at h
      linarith
  · obtain ⟨v,hv⟩ := kc.bddBelow
    refine ⟨v,?_,fun y _ _=> hv (inImage y)⟩
    intro x k g
    exact (ne ⟨V x,mem_image_of_mem V (show x∈M from ⟨k,g⟩)⟩).elim

end LengthGrowth.ActualFlow.PeriodicRegularPosition
#print axioms LengthGrowth.ActualFlow.PeriodicRegularPosition.separating_inflection_velocity
