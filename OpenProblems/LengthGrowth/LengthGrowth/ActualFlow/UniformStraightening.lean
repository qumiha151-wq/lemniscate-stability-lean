import LengthGrowth.ActualFlow.AngularSpeedTail
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

private theorem force_linear_tail (flow : c.IsNormalFEF) :
    ∃ K : ℝ, 0≤K ∧ AntitoneOn (fun t => c.dissipation t+K*c.energy t) (Ici 1) := by
  obtain ⟨M,hm,cap⟩ := c.force_dissipation_tail_bound flow
    (fun _ ht => c.actual_force_dissipation_rate flow ht) (by norm_num : (0:ℝ)<1)
  let K := 2500000*(c.energy 1*M)^(2/3:ℝ)+32*c.energy 1^(1/4:ℝ)*M^(3/4:ℝ)
  have mn : 0≤M := by linarith
  have kn : 0≤K := by dsimp [K]; positivity [c.energy_nonneg 1]
  refine ⟨K,kn,?_⟩
  have diff (t : ℝ) (ht : 1≤t) : HasDerivAt (fun t => c.dissipation t+K*c.energy t)
      (deriv c.dissipation t+K*(-c.dissipation t)) t :=
    (c.dissipation_differentiable_positive (by linarith)).hasDerivAt.add
      ((c.energy_hasDerivAt_normal flow (by linarith)).const_mul K)
  apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
    (fun t ht => (diff t ht).continuousAt.continuousWithinAt)
    (fun t ht => (diff t (interior_subset ht)).differentiableAt.differentiableWithinAt)
  intro t ht
  have ord : 1≤t := interior_subset ht
  rw [(diff t ord).deriv]
  have dn := c.dissipation_nonneg t
  have en := c.energy_nonneg t
  have de := c.energy_le_of_le flow (by norm_num : (0:ℝ)≤1) ord
  have dm := cap t ord
  have cg : 2500000*(c.energy t*c.dissipation t)^(2/3:ℝ)+
       32*c.energy t^(1/4:ℝ)*c.dissipation t^(3/4:ℝ)≤K := by
    dsimp only [K]
    gcongr <;> positivity [c.energy_nonneg 1]
  have q := c.actual_force_dissipation_rate flow (show 0<t by linarith)
  linarith only [c.forceSecondMass_nonneg t,q,mul_le_mul_of_nonneg_right cg dn]

/-- On each trajectory, force dissipation at the end of any late unit time
interval is controlled by that interval's actual drop in bending energy. -/
theorem dissipation_le_unit_energy_drop (flow : c.IsNormalFEF) :
    ∃ C : ℝ, 0<C ∧ ∀s≥1, c.dissipation (s+1)≤C*(c.energy s-c.energy (s+1)) := by
  obtain ⟨K,kn,mono⟩ := c.force_linear_tail flow
  refine ⟨1+K,by linarith,?_⟩
  intro s hs
  have ord : s≤s+1 := by linarith
  have sn : 0≤s := by linarith
  have cont := c.dissipation_continuousOn.mono (show Icc s (s+1)⊆Ici 0 from fun _ ht=>sn.trans ht.1)
  obtain ⟨u,hu,low⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr ord) cont
  have small := intervalIntegral.integral_mono_on (μ:=volume) ord
    (intervalIntegrable_const (c:=c.dissipation u)) (cont.intervalIntegrable_of_Icc ord) (fun z hz => low hz)
  rw [intervalIntegral.integral_const,smul_eq_mul] at small
  have le := mono (show u∈Ici (1:ℝ) from hs.trans hu.1) (show s+1∈Ici (1:ℝ) from hs.trans ord) hu.2
  change c.dissipation (s+1)+K*c.energy (s+1)≤c.dissipation u+K*c.energy u at le
  linarith only [le,small,c.energy_add_integral_dissipation flow sn ord,
    mul_le_mul_of_nonneg_left (c.energy_le_of_le flow sn hu.1) kn]

theorem actual_dissipation_tendsto_zero (flow : c.IsNormalFEF) :
    Tendsto c.dissipation atTop (𝓝 0) := by
  obtain ⟨K,kp,cap⟩ := c.dissipation_le_unit_energy_drop flow
  let S := c.energy '' Ici 1
  have ne : S.Nonempty := ⟨c.energy 1,1,mem_Ici.mpr le_rfl,rfl⟩
  have low : BddBelow S := ⟨0,by rintro _ ⟨x,_,rfl⟩; exact c.energy_nonneg x⟩
  apply tendsto_order.2
  refine ⟨fun z hz => Eventually.of_forall (fun t => hz.trans_le (c.dissipation_nonneg t)),?_⟩
  intro ε ep
  obtain ⟨_,⟨s,hs,rfl⟩,approx⟩ := exists_lt_of_csInf_lt ne
    (show sInf S<sInf S+ε/K from lt_add_of_pos_right _ (div_pos ep kp))
  change 1≤s at hs
  filter_upwards [eventually_ge_atTop (s+1)] with t ht
  have ts : s≤t-1 := by linarith only [ht]
  have g := cap (t-1) (hs.trans ts)
  rw [sub_add_cancel] at g
  have e := c.energy_le_of_le flow (by linarith : 0≤s) ts
  have infimum := csInf_le low (show c.energy t∈S from ⟨t,by change 1≤t; linarith,rfl⟩)
  have err : c.energy (t-1)-c.energy t<ε/K := by linarith only [approx,e,infimum]
  have err' := (lt_div_iff₀ kp).mp err
  linarith only [g,err']

/-- In the original physical units every smooth closed flow straightens
uniformly in both curvature and its first arclength derivative, across every
parameter label. No decay of its total bending energy is assumed. -/
theorem uniform_curvature_and_gradient_decay (flow : c.IsNormalFEF) {ε : ℝ} (ep : 0<ε) :
    ∀ᶠt in atTop, ∀u : ℝ, |curvature (c.position t) u|<ε ∧ |curvatureGradient (c.position t) u|<ε := by
  have d := c.actual_dissipation_tendsto_zero flow
  let e := c.energy 1
  have en : 0≤e := c.energy_nonneg 1
  have eD : Tendsto (fun t => e*c.dissipation t) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x:=e)).mul d
  have p := eD.rpow_const (p:=2/3) (Or.inr (by norm_num))
  have q := d.rpow_const (p:=3/4) (Or.inr (by norm_num))
  have p0 : Tendsto (fun t => (e*c.dissipation t)^(2/3:ℝ)) atTop (𝓝 0) := by simpa using p
  have q0 : Tendsto (fun t => c.dissipation t^(3/4:ℝ)) atTop (𝓝 0) := by simpa using q
  have limK := (tendsto_const_nhds (x:=(65536:ℝ))).mul p0
  have limS := ((tendsto_const_nhds (x:=(16416:ℝ))).mul p0).add
    ((tendsto_const_nhds (x:=4*e^(1/4:ℝ))).mul q0)
  simp only [mul_zero,add_zero] at limK limS
  filter_upwards [limK.eventually_lt_const (pow_pos ep 4),limS.eventually_lt_const (pow_pos ep 2),
    eventually_ge_atTop (1:ℝ)] with t kt st ht
  intro u
  have tn : 0≤t := by linarith
  have et : c.energy t≤e := c.energy_le_of_le flow (by norm_num) ht
  have dn := c.dissipation_nonneg t
  obtain ⟨slope,curv⟩ := c.curvature_gradient_and_fourth_rate_bound tn u
  have cmp := Real.rpow_le_rpow (mul_nonneg (c.energy_nonneg t) dn)
    (mul_le_mul_of_nonneg_right et dn) (by norm_num : (0:ℝ)≤2/3)
  have cp := Real.rpow_le_rpow (c.energy_nonneg t) et (by norm_num : (0:ℝ)≤1/4)
  change 65536*(e*c.dissipation t)^(2/3:ℝ)<ε^4 at kt
  change 16416*(e*c.dissipation t)^(2/3:ℝ)+4*e^(1/4:ℝ)*c.dissipation t^(3/4:ℝ)<ε^2 at st
  constructor
  · apply lt_of_pow_lt_pow_left₀ 4 ep.le
    rw [Even.pow_abs (show Even 4 by decide)]
    linarith only [kt,cmp,curv]
  · apply lt_of_pow_lt_pow_left₀ 2 ep.le
    rw [sq_abs]
    nlinarith only [st,slope,cmp,mul_le_mul_of_nonneg_right cp (Real.rpow_nonneg dn (3/4:ℝ))]

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.actual_dissipation_tendsto_zero
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.uniform_curvature_and_gradient_decay
