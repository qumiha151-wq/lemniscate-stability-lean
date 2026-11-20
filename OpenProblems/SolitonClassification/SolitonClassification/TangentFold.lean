import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.Linarith

/-! A real tangent angle with a periodic, sign-changing derivative has
arbitrarily shallow return arcs above a common endpoint level. -/
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity

private theorem enclosing_zeros {f : ℝ → ℝ} {j p k : ℝ} (hf : Continuous f)
    (hjp : j ≤ p) (hpk : p ≤ k) (hj : f j=0) (hk : f k=0) (hp : 0<f p) :
    ∃ a ∈ Icc j p, ∃ b ∈ Icc p k, f a=0 ∧ f b=0 ∧ ∀ x ∈ Icc a b, 0 ≤ f x := by
  have hs : IsClosed {x : ℝ | f x=0} := isClosed_eq hf continuous_const
  obtain ⟨a,ha,ham⟩ := (isCompact_Icc.inter_right hs).exists_isMaxOn
    (show (Icc j p ∩ {x | f x=0}).Nonempty from ⟨j,⟨le_rfl,hjp⟩,hj⟩) continuous_id.continuousOn
  obtain ⟨b,hb,hbm⟩ := (isCompact_Icc.inter_right hs).exists_isMinOn
    (show (Icc p k ∩ {x | f x=0}).Nonempty from ⟨k,⟨hpk,le_rfl⟩,hk⟩) continuous_id.continuousOn
  refine ⟨a,ha.1,b,hb.1,ha.2,hb.2,?_⟩
  intro x hx
  by_contra! hn
  rcases le_total x p with hxp | hpx
  · obtain ⟨y,hy,hy0⟩ := intermediate_value_Icc hxp hf.continuousOn (show (0:ℝ) ∈ Icc (f x) (f p) from ⟨hn.le,hp.le⟩)
    have hya : y ≤ a := ham ⟨⟨ha.1.1.trans (hx.1.trans hy.1),hy.2⟩,hy0⟩
    have hyx : y=x := le_antisymm (hya.trans hx.1) hy.1
    exact hn.ne (hyx ▸ hy0)
  · obtain ⟨y,hy,hy0⟩ := intermediate_value_Icc' hpx hf.continuousOn (show (0:ℝ) ∈ Icc (f x) (f p) from ⟨hn.le,hp.le⟩)
    have hby : b ≤ y := hbm ⟨⟨hy.1,hy.2.trans (hx.2.trans hb.1.2)⟩,hy0⟩
    have hyx : y=x := le_antisymm hy.2 (hx.2.trans hby)
    exact hn.ne (hyx ▸ hy0)


/-- A positive derivative followed by a negative derivative forces a peak
strictly above both endpoint values, independently of its flatness. -/
private theorem peak_between {θ k : ℝ → ℝ} {u v : ℝ} (hd : ∀ s, HasDerivAt θ (k s) s)
    (huv : u<v) (hu : 0<k u) (hv : k v<0) :
    ∃ m ∈ Icc u v, (∀ x ∈ Icc u v, θ x ≤ θ m) ∧ θ u<θ m ∧ θ v<θ m := by
  have hc : Continuous θ := continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)
  obtain ⟨m,hm,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr huv.le) hc.continuousOn
  have hr := (hasDerivAt_iff_tendsto_slope_left_right.mp (hd u)).2.eventually_const_lt hu
  have hl := (hasDerivAt_iff_tendsto_slope_left_right.mp (hd v)).1.eventually_lt_const hv
  obtain ⟨x,hx,hux,hxv⟩ := (hr.and (Ioo_mem_nhdsGT huv)).exists
  obtain ⟨y,hy,huy,hyv⟩ := (hl.and (Ioo_mem_nhdsLT huv)).exists
  rw [slope_def_field] at hx hy
  have hx' := (lt_div_iff₀ (sub_pos.mpr hux)).mp hx
  have hy' := (div_lt_iff_of_neg (sub_neg.mpr hyv)).mp hy
  refine ⟨m,hm,fun x h => hmax h,?_,?_⟩
  · apply lt_of_lt_of_le _ (show θ x ≤ θ m from hmax ⟨hux.le,hxv.le⟩)
    simpa only [zero_mul,sub_pos] using hx'
  · apply lt_of_lt_of_le _ (show θ y ≤ θ m from hmax ⟨huy.le,hyv.le⟩)
    simpa only [zero_mul,sub_pos] using hy'

/-- With any prescribed positive angular width, there is an arc on which the
lift stays above a common return level, and strictly above it somewhere. -/
theorem exists_upper_angle_fold_of_width {θ k : ℝ → ℝ} {L ε : ℝ} (hL : 0<L)
    (hd : ∀ s, HasDerivAt θ (k s) s) (hp : Function.Periodic k L)
    (hpos : ∃ s, 0<k s) (hneg : ∃ s, k s<0) (hε : 0<ε) :
    ∃ l r m h : ℝ, l<r ∧ m∈Icc l r ∧ θ l=h ∧ θ r=h ∧ 0<θ m-h ∧
      ∀ s∈Icc l r, 0≤θ s-h ∧ θ s-h<ε := by
  obtain ⟨u,hu⟩ := hpos
  obtain ⟨v₀,hv₀⟩ := hneg
  obtain ⟨n,hn⟩ := exists_nat_gt ((u-v₀)/L)
  let v := v₀+(n:ℝ)*L
  have huv : u<v := by
    dsimp [v]
    linarith [(div_lt_iff₀ hL).mp hn]
  have hkv : k v<0 := by
    change k (v₀+(n:ℝ)*L)<0
    rw [(hp.nat_mul n) v₀]
    exact hv₀
  have hc : Continuous θ := continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)
  obtain ⟨m,hm,hmax,hmu,hmv⟩ := peak_between hd huv hu hkv
  let b := max (max (θ u) (θ v)) (θ m-ε)
  have hb : b<θ m := max_lt (max_lt hmu hmv) (by linarith)
  obtain ⟨h,hbh,hhm⟩ := exists_between hb
  have uh : θ u≤h := (le_max_left _ _).trans ((le_max_left _ _).trans hbh.le)
  have vh : θ v≤h := (le_max_right _ _).trans ((le_max_left _ _).trans hbh.le)
  have hwidth : θ m-ε<h := (le_max_right _ _).trans_lt hbh
  obtain ⟨j,hj,hj0⟩ := intermediate_value_Icc hm.1 hc.continuousOn
    (show h ∈ Icc (θ u) (θ m) from ⟨uh,hhm.le⟩)
  obtain ⟨t,ht,ht0⟩ := intermediate_value_Icc' hm.2 hc.continuousOn
    (show h ∈ Icc (θ v) (θ m) from ⟨vh,hhm.le⟩)
  obtain ⟨l,hl,r,hr,hl0,hr0,hreturn⟩ := enclosing_zeros (f := fun x => θ x-h)
    (hc.sub continuous_const) hj.2 ht.1 (sub_eq_zero.mpr hj0) (sub_eq_zero.mpr ht0) (sub_pos.mpr hhm)
  have hlm : l<m := lt_of_le_of_ne hl.2 (by intro he; subst l; linarith)
  refine ⟨l,r,m,h,hlm.trans_le hr.1,⟨hl.2,hr.1⟩,sub_eq_zero.mp hl0,sub_eq_zero.mp hr0,
    sub_pos.mpr hhm,fun s hs => ⟨hreturn s hs,?_⟩⟩
  have hsm := hmax s ⟨hj.1.trans (hl.1.trans hs.1), hs.2.trans (hr.2.trans ht.2)⟩
  linarith

theorem exists_upper_angle_fold {θ k : ℝ → ℝ} {L : ℝ} (hL : 0<L)
    (hd : ∀ s, HasDerivAt θ (k s) s) (hp : Function.Periodic k L)
    (hpos : ∃ s, 0<k s) (hneg : ∃ s, k s<0) (_ck : Continuous k) :
    ∃ l r m h : ℝ, l<r ∧ m∈Icc l r ∧ θ l=h ∧ θ r=h ∧ 0<θ m-h ∧
      ∀ s∈Icc l r, 0≤θ s-h ∧ θ s-h<Real.pi/2 :=
  exists_upper_angle_fold_of_width hL hd hp hpos hneg (half_pos Real.pi_pos)

#print axioms exists_upper_angle_fold_of_width
#print axioms exists_upper_angle_fold
end ClosedSimilarity
