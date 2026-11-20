import LengthGrowth.ActualFlow.FiniteSignGrowth
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section
open Set Filter FreeElasticScalar
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- The additive static estimate in scale-invariant curvature variables. -/
def NodalDeficit (E L D A : ℝ) : Prop :=
  Real.sqrt (E*L) ≤ Real.sqrt (D*L^3/(2*E^2))+A

theorem nodalSliceBound_of_deficit {t A : ℝ} (ht : 0≤t) (hA : 0≤A)
    (hdef : NodalDeficit (c.energy t) (c.length t) (c.dissipation t) A) :
    NodalSliceBound (c.energy t) (c.length t) (c.dissipation t) (A*(1+A)) := by
  let E:=c.energy t
  let L:=c.length t
  let D:=c.dissipation t
  let x:=Real.sqrt (E*L)
  let z:=Real.sqrt (D*L^3/(2*E^2))
  have he:0<E:=c.energy_pos ht
  have hl:0<L:=c.length_pos ht
  have hd:0≤D:=c.dissipation_nonneg _
  have hx:0≤x:=Real.sqrt_nonneg _
  have hz:0≤z:=Real.sqrt_nonneg _
  have xx:x^2=E*L:=Real.sq_sqrt (mul_pos he hl).le
  have zz:z^2*(2*E^2)=D*L^3 := by
    have h:=Real.sq_sqrt (show 0≤D*L^3/(2*E^2) by positivity)
    exact (eq_div_iff (by positivity : 2*E^2≠0)).mp h
  have hv : 4*Real.pi^2*E^2≤D*L^3 := c.sharp_virial ht
  have ez : 1≤z := by
    by_contra! hn
    have h2:=mul_self_lt_mul_self hz hn
    nlinarith only [zz,hv,mul_lt_mul_of_pos_right h2 (by positivity : 0<2*E^2),
      mul_nonneg (show 0≤4*Real.pi^2-2 by nlinarith [Real.pi_gt_three]) (sq_nonneg E)]
  change x≤z+A at hdef
  have bare : x^2 ≤ z*(x+A*(1+A)) := by
    nlinarith only [mul_le_mul_of_nonneg_left hdef hx,mul_le_mul_of_nonneg_left hdef hA,
      mul_nonneg (sq_nonneg A) (sub_nonneg.mpr ez)]
  have sq := mul_self_le_mul_self (sq_nonneg _) bare
  have sm:=mul_le_mul_of_nonneg_right sq (by positivity : 0≤2*E^2)
  have heq : (x^2*x^2)*(2*E^2)=2*E^3*(E*L)*L := by rw [xx];ring
  have heq' : (z*(x+A*(1+A))*(z*(x+A*(1+A))))*(2*E^2)=D*L^2*(x+A*(1+A))^2*L := by
    calc
      _ = (z^2*(2*E^2))*(x+A*(1+A))^2 := by ring
      _ = _ := by rw [zz];ring
  rw [heq,heq'] at sm
  exact (mul_le_mul_iff_left₀ hl).mp sm

theorem nodal_energy_tendsto_zero (hf : c.IsNormalFEF) {T K : ℝ}
    (hT : 0≤T) (hK : 0≤K)
    (hs : ∀t>T, NodalSliceBound (c.energy t) (c.length t) (c.dissipation t) K) :
    Tendsto c.energy atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun t => ha.trans_le (c.energy_nonneg t))
  · intro a ha
    by_contra! hn
    have lower (t:ℝ) (ht:T≤t) : a≤c.energy t := by
      by_contra! h
      apply hn
      filter_upwards [eventually_ge_atTop t] with s hst
      exact not_le.mpr ((c.energy_le_of_le hf (hT.trans ht) hst).trans_lt h)
    have bar:=c.nodal_log_energy_barrier hf hT hK hs
    let B:=Real.sqrt (c.normalizedProduct T)+(K/2)*Real.log (c.energy T)-(K/2)*Real.log a
    have cap (t:ℝ) (ht:T≤t) : c.normalizedProduct t≤B^2 := by
      have h1:=bar (Set.mem_Ici.mpr (le_rfl : T≤T)) (Set.mem_Ici.mpr ht) ht
      have h2:=mul_le_mul_of_nonneg_left (Real.log_le_log ha (lower t ht)) (by positivity : 0≤K/2)
      have h3:Real.sqrt (c.normalizedProduct t)≤B := by dsimp [B]; linarith
      have he:=mul_self_le_mul_self (Real.sqrt_nonneg _) h3
      nlinarith only [he,Real.sq_sqrt (c.normalizedProduct_nonneg t)]
    obtain ⟨u,_,hu⟩:=isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT)
      (c.normalizedProduct_continuousOn.mono (fun _ hx=>hx.1))
    have hb : c.HasBoundedEnergyLength := by
      refine ⟨max (c.normalizedProduct u) (B^2),fun t ht=>?_⟩
      by_cases h:t≤T
      · exact (hu ⟨ht,h⟩).trans (le_max_left _ _)
      · exact (cap t (le_of_not_ge h)).trans (le_max_right _ _)
    obtain ⟨C,hC,upper⟩:=c.quarter_energy_of_quarter_length hf ((c.quarter_length_iff_bounded_energyLength hf).mpr hb)
    have grow : Tendsto (fun t:ℝ=>fourthRoot (1+t)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_left _ _ tendsto_id))
    obtain ⟨t,ht,hh⟩:=((eventually_ge_atTop T).and (grow.eventually_gt_atTop (C/a))).exists
    have pos:0<fourthRoot (1+t):=(div_pos hC ha).trans hh
    have h1:=(le_div_iff₀ pos).mp (upper t (hT.trans ht))
    have h2:=(div_lt_iff₀ ha).mp hh
    nlinarith only [h1,h2,mul_le_mul_of_nonneg_right (lower t ht) pos.le]

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.nodalSliceBound_of_deficit
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.nodal_energy_tendsto_zero
