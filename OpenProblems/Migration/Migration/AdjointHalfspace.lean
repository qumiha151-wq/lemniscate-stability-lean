import Migration.ProjectedAdjoint

/-! The positive adjoint density rules out weak separation even at the
limiting radius. Its zeros cannot contain an open arc. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Adjoint.Frame
variable {rate L : ℝ} (f : Frame rate L)

theorem height_zero_of_nonneg {R : ℝ} (hr : 0<rate) (hL : 0<L)
    (hcap : rate*R^4≤2) (hb : ∀ s, (f.p s)^2+(f.q s)^2≤R^2) (hn : ∀ s, 0≤f.h s) :
    ∀ s, f.h s=0 := by
  let g := fun s => f.density R s*f.h s
  have hk : Continuous f.k := continuous_iff_continuousAt.mpr (fun s => (f.kD s).continuousAt)
  have hp : Continuous f.p := continuous_iff_continuousAt.mpr (fun s => (f.pD s).continuousAt)
  have hq : Continuous f.q := continuous_iff_continuousAt.mpr (fun s => (f.qD s).continuousAt)
  have hh : Continuous f.h := continuous_iff_continuousAt.mpr (fun s => (f.hD s).continuousAt)
  have hc : Continuous g := by dsimp [g,density,weight]; fun_prop
  have hpnt (s) := f.density_nonneg_bound hr hcap s (hb s)
  have hnn (s) : 0≤g s := mul_nonneg ((show 0≤2*rate*(f.q s)^2 by positivity).trans (hpnt s)) (hn s)
  have hg0 : ∀ t ∈ Icc 0 L, g t=0 := by
    intro t ht
    by_contra hne
    have hpos := lt_of_le_of_ne (hnn t) (Ne.symm hne)
    have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (f := fun _ : ℝ => (0:ℝ)) (g := g) hL continuous_const.continuousOn hc.continuousOn
      (fun u _ => hnn u) ⟨t,ht,hpos⟩
    change (∫ _ in (0:ℝ)..L, (0:ℝ)) < ∫ s in 0..L, f.density R s*f.h s at h
    rw [intervalIntegral.integral_zero,f.weighted_height_integral R] at h
    exact (lt_irrefl _ h)
  have hper : Function.Periodic g L := by
    intro s
    obtain ⟨hk',_,hp',hq',hh',_,_⟩ := f.periodic s
    dsimp [g,density,weight]
    rw [hk',hp',hq',hh']
  have hzero (s) : g s=0 := by
    obtain ⟨t,ht,he⟩ := hper.exists_mem_Ico₀ hL s
    exact he.trans (hg0 t ⟨ht.1,ht.2.le⟩)
  intro s
  by_contra hne
  have hpos := lt_of_le_of_ne (hn s) (Ne.symm hne)
  have hqnear : f.q =ᶠ[𝓝 s] fun _ => 0 := by
    filter_upwards [hh.continuousAt.eventually (lt_mem_nhds hpos)] with z hz
    have hden : f.density R z=0 := (mul_eq_zero.mp (hzero z)).resolve_right hz.ne'
    have hqz := hpnt z
    rw [hden] at hqz
    by_contra hqne
    exact (not_lt_of_ge hqz) (mul_pos (by positivity) (sq_pos_of_ne_zero hqne))
  have hqz : f.q s=0 := hqnear.eq_of_nhds
  have hd := (f.qD s).unique ((hasDerivAt_const s (0:ℝ)).congr_of_eventuallyEq hqnear)
  have hkp : f.k s*f.p s= -1 := by linarith
  have hkn : f.k s≠0 := by intro hz; rw [hz,zero_mul] at hkp; norm_num at hkp
  have hw : f.weight R s≤R^2 := by dsimp [weight]; linarith [hb s]
  have hden : f.density R s=0 := (mul_eq_zero.mp (hzero s)).resolve_right hne
  unfold density at hden
  rw [hqz,show rate*f.k s*f.p s= -rate by rw [mul_assoc,hkp]; ring] at hden
  nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hw),sq_pos_of_ne_zero hkn]

end MigrationGeometry.Adjoint.Frame
