import Migration.ForwardHalfplaneCost
import Mathlib.Topology.Order.IntermediateValue

/-! A full material period contains a monotone-height excursion passing
through a vertical tangent, for either choice of orientation of the plane. -/
noncomputable section
open Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow

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

theorem tangent_components_sq {γ : ℝ → ℂ} (hr : ∀ u, deriv γ u ≠ 0) (u : ℝ) :
    (tangent γ u).re^2+(tangent γ u).im^2=1 := by
  have h := Complex.normSq_eq_norm_sq (tangent γ u)
  rw [tangent_unit hr,Complex.normSq_apply] at h
  nlinarith

theorem tangent_excursion {γ : ℝ → ℂ} {P : ℝ} (hP : 0<P)
    (hγ : ContDiff ℝ ∞ γ) (hr : ∀ u, deriv γ u ≠ 0) (hc : Function.Periodic γ P) :
    ∃ j a p b σ : ℝ, j≤a ∧ a≤p ∧ p≤b ∧ b≤j+P ∧ (σ=1 ∨ σ= -1) ∧
      (tangent γ p).re=0 ∧ (tangent γ a).im=0 ∧ (tangent γ b).im=0 ∧
      ∀ x ∈ Icc a b, 0 ≤ σ*(tangent γ x).im := by
  have hy (u : ℝ) : HasDerivAt (fun x => (γ x).im) (speed γ u*(tangent γ u).im) u := by
    apply (Complex.imCLM.hasFDerivAt.comp_hasDerivAt u (position_hasDerivAt hγ hr u)).congr_deriv
    simp
  have hx (u : ℝ) : HasDerivAt (fun x => (γ x).re) (speed γ u*(tangent γ u).re) u := by
    apply (Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (position_hasDerivAt hγ hr u)).congr_deriv
    simp
  have hend : γ P=γ 0 := by simpa using hc 0
  obtain ⟨j,_,hj⟩ := exists_hasDerivAt_eq_zero hP (Complex.continuous_im.comp hγ.continuous).continuousOn
    (show (γ 0).im=(γ P).im by rw [hend]) (fun u _ => hy u)
  obtain ⟨p,hp,hp0⟩ := exists_hasDerivAt_eq_zero (show j<j+P by linarith)
    (Complex.continuous_re.comp hγ.continuous).continuousOn (show (γ j).re=(γ (j+P)).re by rw [hc j])
    (fun u _ => hx u)
  have hj0 : (tangent γ j).im=0 := (mul_eq_zero.mp hj).resolve_left (speed_pos hr j).ne'
  have hpx : (tangent γ p).re=0 := (mul_eq_zero.mp hp0).resolve_left (speed_pos hr p).ne'
  have hpunit := tangent_components_sq hr p
  rw [hpx] at hpunit
  have hpn : (tangent γ p).im≠0 := by intro hz; rw [hz] at hpunit; norm_num at hpunit
  let σ : ℝ := if 0 < (tangent γ p).im then 1 else -1
  have hσ : σ=1 ∨ σ= -1 := by dsimp [σ]; split <;> simp
  have hσn : σ≠0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hpos : 0<σ*(tangent γ p).im := by
    dsimp [σ]
    split
    · next h => simpa using h
    · next h => simpa using (lt_of_le_of_ne (le_of_not_gt h) hpn)
  have htf := Complex.continuous_im.comp (tangent_smooth hγ hr).continuous
  obtain ⟨a,ha,b,hb,ha0,hb0,hf⟩ := enclosing_zeros (f := fun u => σ*(tangent γ u).im)
    (continuous_const.mul htf) hp.1.le hp.2.le (by rw [hj0,mul_zero])
    (by rw [tangent_periodic hγ hc j,hj0,mul_zero]) hpos
  exact ⟨j,a,p,b,σ,ha.1,ha.2,hb.1,hb.2,hσ,hpx,(mul_eq_zero.mp ha0).resolve_left hσn,
    (mul_eq_zero.mp hb0).resolve_left hσn,hf⟩

end MigrationGeometry.Flow
