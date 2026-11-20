import Migration.DirectionalWidth
import Migration.EnergyTransit

noncomputable section
open Set Filter
open scoped Topology
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion

variable (c : SmoothPeriodicImmersion (Ioi 0))

def supportBottom (H : ℂ →L[ℝ] ℝ) (t : ℝ) :=
  sInf ((fun u => H (c.position t u)) '' Icc 0 c.period)
def supportTop (H : ℂ →L[ℝ] ℝ) (t : ℝ) :=
  sSup ((fun u => H (c.position t u)) '' Icc 0 c.period)

private theorem exact_support_range (H : ℂ →L[ℝ] ℝ) {t : ℝ}
    (hc : Continuous (c.position t)) :
    c.HasHeightRange H t (c.supportBottom H t) (c.supportTop H t) := by
  let f := fun u => H (c.position t u)
  have ch : Continuous f := H.continuous.comp hc
  have hne : (Icc 0 c.period).Nonempty := ⟨0,le_rfl,c.period_pos.le⟩
  obtain ⟨u,hu,hm⟩ := isCompact_Icc.exists_isMinOn hne ch.continuousOn
  obtain ⟨v,hv,hM⟩ := isCompact_Icc.exists_isMaxOn hne ch.continuousOn
  have lo : c.supportBottom H t = f u := (show IsLeast (f '' Icc 0 c.period) (f u) from
    ⟨⟨u,hu,rfl⟩,by rintro _ ⟨i,hi,rfl⟩; exact hm hi⟩).csInf_eq
  have hi : c.supportTop H t = f v := (show IsGreatest (f '' Icc 0 c.period) (f v) from
    ⟨⟨v,hv,rfl⟩,by rintro _ ⟨i,hi,rfl⟩; exact hM hi⟩).csSup_eq
  rw [lo,hi]
  exact ⟨fun _ hx => ⟨hm hx,hM hx⟩,⟨u,hu,rfl⟩,⟨v,hv,rfl⟩⟩

theorem forward_initial_directional_width
    (hposition : ContinuousOn (fun z : ℝ × ℝ => c.position z.1 z.2) (Ici 0 ×ˢ univ))
    (henergy : ContinuousWithinAt c.bending (Ici 0) 0) (e : ℂ) (he : ‖e‖ = 1) :
    ∃ lo hi, c.HasHeightRange (innerSL ℝ e) 0 lo hi ∧ 2 ≤ c.bending 0*(hi-lo) := by
  let H : ℂ →L[ℝ] ℝ := innerSL ℝ e
  have hc : Continuous (fun z : ℝ × ℝ => c.position (max z.1 0) z.2) :=
    hposition.comp_continuous ((continuous_fst.max continuous_const).prodMk continuous_snd)
      (fun z => ⟨show 0≤max z.1 0 from le_max_right _ _,mem_univ _⟩)
  have hcz : Continuous (c.position 0) := by
    simpa only [Function.comp_def,max_self,id_eq] using
      hc.comp ((continuous_const : Continuous (fun _ : ℝ => (0:ℝ))).prodMk continuous_id)
  have hh : Continuous (fun z : ℝ × ℝ => H (c.position (max z.1 0) z.2)) := H.continuous.comp hc
  have hlo : Continuous (fun t : ℝ => c.supportBottom H (max t 0)) :=
    isCompact_Icc.continuous_sInf (f := fun t u => H (c.position (max t 0) u)) hh
  have hhi : Continuous (fun t : ℝ => c.supportTop H (max t 0)) :=
    isCompact_Icc.continuous_sSup (f := fun t u => H (c.position (max t 0) u)) hh
  have hw : ContinuousOn (fun t => c.supportTop H t-c.supportBottom H t) (Ici 0) :=
    (hhi.sub hlo).continuousOn.congr (fun t ht => by simp [max_eq_left (show 0≤t from ht)])
  have sub : Ioi (0:ℝ) ⊆ Ici 0 := fun _ h => le_of_lt (show (0:ℝ)<_ from h)
  have hlim := (henergy.mono sub).tendsto.mul (((hw 0 (by simp)).mono sub).tendsto)
  refine ⟨c.supportBottom H 0,c.supportTop H 0,c.exact_support_range H hcz,?_⟩
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  obtain ⟨lo,hi,hr,hb⟩ := c.directional_width_range ht e he
  have hr' := c.exact_support_range H (c.position_slice_smooth ht).continuous
  obtain ⟨u,hu,hwlo⟩ := hr.2.1
  obtain ⟨v,hv,hwhi⟩ := hr.2.2
  have hlow := (hr'.1 u hu).1
  have hhigh := (hr'.1 v hv).2
  change H (c.position t u)=lo at hwlo
  change H (c.position t v)=hi at hwhi
  rw [hwlo] at hlow
  rw [hwhi] at hhigh
  exact hb.trans (mul_le_mul_of_nonneg_left (sub_le_sub hhigh hlow) (c.bending_nonneg t))

#print axioms forward_initial_directional_width
end MigrationGeometry.Flow.SmoothPeriodicImmersion
