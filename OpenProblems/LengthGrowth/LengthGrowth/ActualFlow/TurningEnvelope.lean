import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter
open scoped Topology

namespace LengthGrowth.ActualFlow.TurningEnvelope

/-- A decreasing first variation rules out a spacetime maximum after
    the initial time, even when the optimizing configuration jumps. -/
theorem compact_comparison {X : Type*} [TopologicalSpace X]
    {K : Set X} (hk : IsCompact K) {a b A : ℝ} (_hab : a≤b)
    (f : ℝ×X → ℝ) (hf : ContinuousOn f (Icc a b ×ˢ K))
    (init : ∀ x∈K, f (a,x)≤A)
    (slope : ∀ t∈Ioc a b, ∀ x∈K, (∀ y∈K, f (t,y)≤f (t,x)) →
      ∃ v<0, HasDerivAt (fun s => f (s,x)) v t) :
    ∀ p∈Icc a b ×ˢ K, f p≤A := by
  intro p hp
  obtain ⟨q,hq,top⟩ := (isCompact_Icc.prod hk).exists_isMaxOn ⟨p,hp⟩ hf
  apply (top hp).trans
  rcases eq_or_lt_of_le hq.1.1 with h|h
  · simpa only [h] using init q.2 hq.2
  have slice (y : X) (hy : y∈K) : f (q.1,y)≤f q := top ⟨hq.1,hy⟩
  obtain ⟨v,neg,df⟩ := slope q.1 ⟨h,hq.1.2⟩ q.2 hq.2 slice
  have left := (hasDerivAt_iff_tendsto_slope_left_right.mp df).1
  obtain ⟨r,near,rt,negSlope⟩ := (((lt_mem_nhds h).filter_mono nhdsWithin_le_nhds).and
    ((show ∀ᶠ r in 𝓝[<] q.1, r<q.1 from self_mem_nhdsWithin).and
     (left.eventually (gt_mem_nhds neg)))).exists
  have better := top (show (r,q.2)∈Icc a b ×ˢ K from ⟨⟨near.le,rt.le.trans hq.1.2⟩,hq.2⟩)
  change f (r,q.2) ≤ f (q.1,q.2) at better
  rw [slope_def_field] at negSlope
  rcases div_neg_iff.mp negSlope with u|u
  · exact False.elim (by exact (not_lt_of_ge better) (sub_pos.mp u.1))
  · exact False.elim (by exact (not_lt_of_gt rt) (sub_pos.mp u.2))

end LengthGrowth.ActualFlow.TurningEnvelope
#print axioms LengthGrowth.ActualFlow.TurningEnvelope.compact_comparison
