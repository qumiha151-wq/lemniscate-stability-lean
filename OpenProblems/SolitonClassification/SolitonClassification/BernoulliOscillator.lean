import SolitonClassification.TangentLawGeometry
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
open Set Function Filter
open scoped Topology ContDiff
namespace ClosedSimilarity.BernoulliGeometry
set_option backward.isDefEq.respectTransparency false

private def field (x : ℝ×ℝ) : ℝ×ℝ := (x.2,-2/9*x.1^3)

/-- The quartic curvature oscillator is determined on the full real line
by its initial curvature and curvature derivative. -/
theorem oscillator_unique {k v p q : ℝ→ℝ} {s₀ : ℝ}
    (dk : ∀s,HasDerivAt k (v s) s) (dv : ∀s,HasDerivAt v (-2/9*k s^3) s)
    (dp : ∀s,HasDerivAt p (q s) s) (dq : ∀s,HasDerivAt q (-2/9*p s^3) s)
    (ke : k s₀=p s₀) (ve : v s₀=q s₀) : ∀ s,k s=p s ∧ v s=q s := by
  let f (s : ℝ) := (k s,v s)
  let g (s : ℝ) := (p s,q s)
  have hf (s : ℝ) : HasDerivAt f (field (f s)) s := (dk s).prodMk (dv s)
  have hg (s : ℝ) : HasDerivAt g (field (g s)) s := (dp s).prodMk (dq s)
  have cf : Continuous f := continuous_iff_continuousAt.mpr (fun s=>(hf s).continuousAt)
  have cg : Continuous g := continuous_iff_continuousAt.mpr (fun s=>(hg s).continuousAt)
  have sf : ContDiff ℝ 1 field := by unfold field;fun_prop
  let E := {x | f x=g x}
  have closed : IsClosed E := isClosed_eq cf cg
  have opened : IsOpen E := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have ex : f x=g x := hx
    obtain ⟨K,V,Vx,loc⟩ := (sf.contDiffAt (x:=f x)).exists_lipschitzOnWith
    have fv : ∀ᶠ t in 𝓝 x,f t∈V := cf.continuousAt Vx
    have gv : ∀ᶠ t in 𝓝 x,g t∈V := cg.continuousAt (ex ▸ Vx)
    exact ODE_solution_unique_of_eventually (v:=fun _=>field) (s:=fun _=>V)
      (Eventually.of_forall (fun _=>loc)) (fv.mono (fun t ht=>⟨hf t,ht⟩))
      (gv.mono (fun t ht=>⟨hg t,ht⟩)) ex
  have all := (show IsClopen E from ⟨closed,opened⟩).eq_univ ⟨s₀,Prod.ext ke ve⟩
  intro s
  exact Prod.mk.inj (show s∈E from all.symm ▸ mem_univ s)

private theorem upward {k v : ℝ→ℝ} {L x y : ℝ} (hL : 0<L)
    (per : Periodic k L) (dk : ∀s,HasDerivAt k (v s) s) (hx : k x<0) (hy : 0<k y) :
    ∃s,k s=0 ∧ 0≤v s := by
  have ck : Continuous k := continuous_iff_continuousAt.mpr (fun s=>(dk s).continuousAt)
  obtain ⟨b,hb,eb⟩ := per.exists_mem_Ico hL y x
  have bypos : 0<k b := eb ▸ hy
  let Z := Icc x b ∩ k ⁻¹' ({0}:Set ℝ)
  obtain ⟨s',hs',hz'⟩ := intermediate_value_Icc hb.1 ck.continuousOn
    (show (0:ℝ)∈Icc (k x) (k b) from ⟨hx.le,bypos.le⟩)
  have compact : IsCompact Z := isCompact_Icc.inter_right (isClosed_singleton.preimage ck)
  obtain ⟨s,hs,hm⟩ := compact.exists_isMinOn ⟨s',hs',hz'⟩ continuous_id.continuousOn
  have ks : k s=0 := hs.2
  have xs : x<s := lt_of_le_of_ne hs.1.1 (by rintro rfl;linarith)
  refine ⟨s,ks,ge_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp (dk s)).1 ?_⟩
  filter_upwards [Ioo_mem_nhdsLT xs] with t ht
  have tk : k t<0 := by
    by_contra! htpos
    obtain ⟨u,hu,ku⟩ := intermediate_value_Icc ht.1.le ck.continuousOn
      (show (0:ℝ)∈Icc (k x) (k t) from ⟨hx.le,htpos⟩)
    have su : s≤u := hm (show u∈Z from ⟨⟨hu.1,hu.2.trans (ht.2.le.trans hs.1.2)⟩,ku⟩)
    linarith [hu.2,ht.2]
  rw [slope_def_field,ks,sub_zero]
  exact div_nonneg_of_nonpos tk.le (sub_nonpos.mpr ht.2.le)

theorem oscillator_marker {a b L : ℝ} (z : PeriodicSupportProfile a b L) (hL : 0<L)
    (dv : ∀s,HasDerivAt z.v (-2/9*z.k s^3) s) : ∃s,z.k s=0 ∧ 0<z.v s := by
  have nc : ¬∃K,∀s,z.k s=K := by
    rintro ⟨K,r⟩
    have zero (s : ℝ) : z.v s=0 := by
      have d := z.dk s
      rw [show z.k=fun _=>K from funext r] at d
      exact d.unique (hasDerivAt_const _ _)
    have d := dv 0
    rw [show z.v=fun _=>0 from funext zero] at d
    have k := d.unique (hasDerivAt_const _ _)
    rw [r] at k
    have nz : K=0 := by simpa using k
    have positive := z.bending_pos_of_period hL
    simp [PeriodicSupportProfile.bending,r,nz] at positive
  obtain ⟨⟨x,hx⟩,y,hy⟩ := z.both_curvature_excursions_of_period hL nc
  have hr := z.curvatureRMS_pos (z.dilation_pos hL) hL
  obtain ⟨s,ks,vs⟩ := upward hL z.periodic_k z.dk (x:=x) (y:=y) (by linarith) (by linarith)
  refine ⟨s,ks,lt_of_le_of_ne vs ?_⟩
  intro ez
  have zero := oscillator_unique z.dk dv (p:=fun _=>0) (q:=fun _=>0)
    (fun s=>hasDerivAt_const _ _) (fun s=>by simpa using hasDerivAt_const s (0:ℝ)) ks ez.symm
  exact nc ⟨0,fun s=>(zero s).1⟩

end ClosedSimilarity.BernoulliGeometry
