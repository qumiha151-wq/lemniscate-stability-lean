import SolitonClassification.TangentFold
import SolitonClassification.TangentForceChord

/-! Single-valued force on the oriented tangent characterizes round
periodic similarity profiles. No regularity of the force law is needed. -/
noncomputable section
namespace ClosedSimilarity.PeriodicSupportProfile
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

theorem circle_of_equal_angle_force {a b L : ℝ}
    (z : PeriodicSupportProfile a b L) (hL : 0<L) {θ : ℝ→ℝ}
    (ht : ∀s, HasDerivAt θ (z.k s) s)
    (law : ∀ l r, θ l=θ r → z.force l=z.force r) :
    ∃ c : ℝ, c ≠ 0 ∧ c^4=2*a ∧ (∀ s,z.k s=c) ∧ (∀ s,z.v s=0) ∧
      (∀ s,z.p s= -1/c) ∧ (∀ s,z.q s=0) := by
  apply z.one_sign_centered_circle_of_period hL
  by_cases hpos : ∀s,0≤z.k s
  · exact Or.inl hpos
  by_cases hneg : ∀s,z.k s≤0
  · exact Or.inr hneg
  push Not at hpos hneg
  exfalso
  have ct := continuous_iff_continuousAt.mpr (fun s => (ht s).continuousAt)
  have ha := z.dilation_pos hL
  by_cases hb : 0≤b
  · obtain ⟨l,r,m,h,hlr,hm,hl,hr,hp,band⟩ :=
      exists_upper_angle_fold hL ht z.periodic_k hneg hpos z.continuous_k
    have pos := positive_force_projection_on_fold ha hb ct hlr hm hp band
    rw [z.equal_angle_force_difference ht hl hr,law l r (hl.trans hr.symm),sub_self] at pos
    exact lt_irrefl _ pos
  · have hd (s : ℝ) : HasDerivAt (fun u => -θ u) (-z.k s) s := (ht s).neg
    obtain ⟨x,hx⟩ := hpos
    obtain ⟨y,hy⟩ := hneg
    obtain ⟨l,r,m,h,hlr,hm,hl,hr,hp,band⟩ := exists_upper_angle_fold hL hd
      (fun s => congrArg Neg.neg (z.periodic_k s)) (show ∃s,0< -z.k s from ⟨x,neg_pos.mpr hx⟩)
      (show ∃s,-z.k s<0 from ⟨y,neg_neg_of_pos hy⟩) z.continuous_k.neg
    change -θ l=h at hl
    change -θ r=h at hr
    have hl' : θ l= -h := by linarith
    have hr' : θ r= -h := by linarith
    have pos := positive_force_projection_on_fold ha (show 0≤ -b by linarith)
      ct.neg hlr hm hp band
    have eq : (∫ s in l..r, a*Real.sin (-θ s-h)+(-b)*Real.cos (-θ s-h)) =
        -(∫ s in l..r, a*Real.sin (θ s- -h)+b*Real.cos (θ s- -h)) := by
      rw [←intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      rw [show -θ s-h= -(θ s- -h) by ring,Real.sin_neg,Real.cos_neg]
      ring
    change 0 < ∫ s in l..r, a*Real.sin (-θ s-h)+(-b)*Real.cos (-θ s-h) at pos
    rw [eq,z.equal_angle_force_difference ht hl' hr',law l r (hl'.trans hr'.symm),
      sub_self,neg_zero] at pos
    exact lt_irrefl _ pos

end ClosedSimilarity.PeriodicSupportProfile

#print axioms ClosedSimilarity.PeriodicSupportProfile.circle_of_equal_angle_force
