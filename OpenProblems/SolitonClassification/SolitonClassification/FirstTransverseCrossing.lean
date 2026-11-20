import SolitonClassification.MovingSeamSlab
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSimilarity.GlobalSupport.MovingSeam

private theorem descending_sides {g : ℝ→ℝ} {t d H : ℝ} (hit : g t=H) (der : HasDerivAt g d t)
    (neg : d<0) :
    (∀ᶠ s in 𝓝[<] t, H<g s) ∧ (∀ᶠ s in 𝓝[>] t, g s<H) := by
  obtain ⟨left,right⟩ := hasDerivAt_iff_tendsto_slope_left_right.mp der
  constructor
  · filter_upwards [left.eventually (gt_mem_nhds neg),eventually_mem_nhdsWithin (s:=Iio t)] with s h hs
    rw [slope_def_field,hit] at h
    rcases (div_neg_iff.mp h) with h | h
    · exact sub_pos.mp h.1
    · linarith [h.2,show s<t from hs]
  · filter_upwards [right.eventually (gt_mem_nhds neg),eventually_mem_nhdsWithin (s:=Ioi t)] with s h hs
    rw [slope_def_field,hit] at h
    rcases (div_neg_iff.mp h) with h | h
    · linarith [h.2,show t<s from hs]
    · exact sub_neg.mp h.1

private theorem no_ascending_crossing {g : ℝ→ℝ} {S T H : ℝ}
    (cont : ContinuousOn g (Icc S T))
    (cross : ∀t∈Icc S T, g t=H → ∀ᶠ s in 𝓝[<] t, H<g s)
    (st : S≤T) (low : g S<H) (high : H<g T) : False := by
  let K := {x ∈ Icc S T | g x=H}
  have comp : IsCompact K := isCompact_Icc.of_isClosed_subset
    (isClosed_Icc.isClosed_eq cont continuousOn_const) (fun _ hx => hx.1)
  obtain ⟨v,hv,eq⟩ := intermediate_value_Icc st cont (show H∈Icc (g S) (g T) from ⟨low.le,high.le⟩)
  obtain ⟨t,ht,first⟩ := comp.exists_isMinOn (show K.Nonempty from ⟨v,hv,eq⟩) continuous_id.continuousOn
  have gt : S<t := lt_of_le_of_ne ht.1.1 (by intro h; exact low.ne (h ▸ ht.2))
  have above := cross t ht.1 ht.2
  obtain ⟨u,hu,ut,val⟩ := (((lt_mem_nhds gt).filter_mono nhdsWithin_le_nhds).and
    ((show ∀ᶠ s in 𝓝[<] t, s<t from self_mem_nhdsWithin).and above)).exists
  obtain ⟨w,hw,zero⟩ := intermediate_value_Icc hu.le (cont.mono (Icc_subset_Icc_right (ut.le.trans ht.1.2)))
    (show H∈Icc (g S) (g u) from ⟨low.le,val.le⟩)
  exact not_lt_of_ge (first (show w∈K from ⟨⟨hw.1,(hw.2.trans ut.le).trans ht.1.2⟩,zero⟩)) (hw.2.trans_lt ut)

theorem unique_descending_crossing {g : ℝ→ℝ} {S T H : ℝ}
    (cont : ContinuousOn g (Icc S T))
    (der : ∀t∈Icc S T, g t=H → ∃d<0, HasDerivAt g d t)
    {u v : ℝ} (hu : u∈Icc S T) (hv : v∈Icc S T) (zu : g u=H) (zv : g v=H) : u=v := by
  have sides (t : ℝ) (ht : t∈Icc S T) (eq : g t=H) :
      (∀ᶠ x in 𝓝[<] t,H<g x) ∧ (∀ᶠ x in 𝓝[>] t,g x<H) := by
    obtain ⟨d,neg,D⟩ := der t ht eq
    exact descending_sides eq D neg
  have imposs (a b : ℝ) (ha : a∈Icc S T) (hb : b∈Icc S T) (za : g a=H) (zb : g b=H) (ab : a<b) : False := by
    obtain ⟨p,ap,pb,low⟩ := ((show ∀ᶠ x in 𝓝[>] a,a<x from self_mem_nhdsWithin).and
      (((gt_mem_nhds ab).filter_mono nhdsWithin_le_nhds).and (sides a ha za).2)).exists
    obtain ⟨q,pq,qb,high⟩ := (((lt_mem_nhds pb).filter_mono nhdsWithin_le_nhds).and
      ((show ∀ᶠ x in 𝓝[<] b,x<b from self_mem_nhdsWithin).and (sides b hb zb).1)).exists
    have sub : Icc p q ⊆ Icc S T := Icc_subset_Icc (ha.1.trans ap.le) (qb.le.trans hb.2)
    exact no_ascending_crossing (cont.mono sub) (fun t ht eq => (sides t (sub ht) eq).1)
      pq.le low high
  rcases lt_trichotomy u v with h|h|h
  · exact (imposs u v hu hv zu zv h).elim
  · exact h
  · exact (imposs v u hv hu zv zu h).elim

private theorem uniform_strict_before {X : Type*} [TopologicalSpace X] {F : X×ℝ→ℝ} {x : X}
    {S t H : ℝ} (hc : ∀s∈Icc S t, ContinuousAt F (x,s))
    (strict : ∀s∈Icc S t, H<F (x,s)) :
    ∀ᶠ y in 𝓝 x, ∀s∈Icc S t, H<F (y,s) := by
  let V := {p : ℝ×X | H<F (p.2,p.1)}
  have all (s : ℝ) (hs : s∈Icc S t) : V∈𝓝 (s,x) := by
    have lim : Tendsto (fun p : ℝ×X => F (p.2,p.1)) (𝓝 (s,x)) (𝓝 (F (x,s))) :=
      (hc s hs).tendsto.comp (continuous_swap.tendsto (s,x))
    exact lim.eventually (lt_mem_nhds (strict s hs))
  have mem := isCompact_Icc.mem_nhdsSet_prod_of_forall (s:=V) (l:=𝓝 x) (fun s hs => by
    rw [←nhds_prod_eq]; exact all s hs)
  obtain ⟨U,hU,W,hW,hsub⟩ := mem_prod_iff.mp mem
  apply Filter.mem_of_superset hW
  intro y hy s hs
  change (s,y)∈V
  exact hsub (show (s,y)∈U×ˢW from ⟨subset_of_mem_nhdsSet hU hs,hy⟩)

/-- Variable outer exit times need no regularity. The first crossing of a
    fixed level varies continuously when the height is jointly continuous
    along the flight and each crossing has strictly negative time derivative.
    The trajectory can later re-enter the same level outside the flight. -/
theorem continuous_first_crossing {X : Type*} [TopologicalSpace X] (F : X×ℝ→ℝ) (S H : ℝ)
    (flight : X→ℝ) (bounds : ∀x, S<flight x ∧ H<F (x,S) ∧ F (x,flight x)<H)
    (ct : ∀x s, s∈Icc S (flight x) → ContinuousAt F (x,s))
    (speed : ∀x s, s∈Icc S (flight x) → F (x,s)=H →
      ∃d<0,HasDerivAt (fun t => F (x,t)) d s) :
    ∃ τ : X→ℝ, Continuous τ ∧ ∀x,
      τ x∈Ioo S (flight x) ∧ F (x,τ x)=H ∧
      (∀s∈Icc S (flight x), F (x,s)=H → s=τ x) ∧
      (∀s∈Ico S (τ x), H<F (x,s)) := by
  have cont (x : X) : ContinuousOn (fun t => F (x,t)) (Icc S (flight x)) := fun s hs =>
    ((ct x s hs).comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have hit (x : X) := intermediate_value_Ioo' (bounds x).1.le (cont x)
    (show H∈Ioo (F (x,flight x)) (F (x,S)) from ⟨(bounds x).2.2,(bounds x).2.1⟩)
  choose τ inside eq using hit
  have only (x : X) (s : ℝ) (hs : s∈Icc S (flight x)) (same : F (x,s)=H) : s=τ x :=
    unique_descending_crossing (cont x) (speed x) hs (Ioo_subset_Icc_self (inside x)) same (eq x)
  have before (x : X) (s : ℝ) (hs : s∈Ico S (τ x)) : H<F (x,s) := by
    by_contra! below
    obtain ⟨t,ht,zero⟩ := intermediate_value_Icc' hs.1
      ((cont x).mono (Icc_subset_Icc_right (hs.2.trans (inside x).2).le))
      (show H∈Icc (F (x,s)) (F (x,S)) from ⟨below,(bounds x).2.1.le⟩)
    have same := only x t ⟨ht.1,(ht.2.trans hs.2.le).trans (inside x).2.le⟩ zero
    linarith [ht.2,hs.2]
  refine ⟨τ,?_,fun x => ⟨inside x,eq x,only x,before x⟩⟩
  rw [continuous_iff_continuousAt]
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let L := τ x-ε/2
  have Llt : L<τ x := by dsimp [L]; linarith
  have prior := uniform_strict_before (F:=F) (S:=S) (t:=L) (H:=H)
    (fun s hs => ct x s ⟨hs.1,(hs.2.trans Llt.le).trans (inside x).2.le⟩)
    (fun s hs => before x s ⟨hs.1,hs.2.trans_lt Llt⟩)
  obtain ⟨d,hd,D⟩ := speed x (τ x) (Ioo_subset_Icc_self (inside x)) (eq x)
  have neg := (descending_sides (eq x) D hd).2
  have close : τ x < min (flight x) (τ x+ε) := lt_min (inside x).2 (by linarith)
  obtain ⟨r,right,less,negative⟩ :=
    ((show ∀ᶠ r in 𝓝[>] (τ x), τ x<r from self_mem_nhdsWithin).and
      (((gt_mem_nhds close).filter_mono nhdsWithin_le_nhds).and neg)).exists
  have hr : r ∈ Icc S (flight x) := ⟨((inside x).1.trans right).le,(lt_min_iff.mp less).1.le⟩
  have late : ∀ᶠ y in 𝓝 x, F (y,r)<H := by
    have lim : Tendsto (fun y : X => F (y,r)) (𝓝 x) (𝓝 (F (x,r))) :=
      (ct x r hr).tendsto.comp ((continuous_id.prodMk (continuous_const (y:=r))).tendsto x)
    exact lim.eventually (gt_mem_nhds negative)
  filter_upwards [prior,late] with y earlier later
  have lo : L<τ y := by
    by_contra! early
    exact ((earlier (τ y) ⟨(inside y).1.le,early⟩).ne' (eq y))
  have hi : τ y≤r := by
    by_contra! aft
    exact (not_lt_of_gt (before y r ⟨hr.1,aft⟩)) later
  rw [Real.dist_eq,abs_lt]
  dsimp [L] at lo
  exact ⟨by linarith,by linarith [(lt_min_iff.mp less).2]⟩

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.continuous_first_crossing
