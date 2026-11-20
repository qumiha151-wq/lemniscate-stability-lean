import LengthGrowth.ActualFlow.SharpVirial
import LengthGrowth.ActualFlow.RelativeEnergy
import LengthGrowth.ActualFlow.GrowthEquivalence
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace LengthGrowth.ActualFlow.ForwardImmersion

/-- A static inequality for the three material integrals. Its inverse-ratio
form is convenient on all product scales. -/
def NodalSliceBound (E L D K : ℝ) : Prop :=
  2*E^3*(E*L) ≤ D*L^2*(Real.sqrt (E*L)+K)^2

private theorem nodal_rate {E L D v K : ℝ} (he : 0<E) (hl : 0<L) (hd : 0≤D) (hK : 0≤K)
    (hv : v^2≤2*E*D) (hs : NodalSliceBound E L D K) :
    E*(E*v-L*D)≤K*Real.sqrt (E*L)*D := by
  let x:=Real.sqrt (E*L)
  have hx : 0<x := Real.sqrt_pos.mpr (mul_pos he hl)
  have xx : x^2=E*L := Real.sq_sqrt (mul_pos he hl).le
  change 2*E^3*(E*L)≤D*L^2*(x+K)^2 at hs
  have sq : (E*v*x)^2≤(L*D*(x+K))^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hv (mul_nonneg (sq_nonneg E) (sq_nonneg x)),
      mul_le_mul_of_nonneg_left hs hd,show E^3*D*x^2=E^3*D*(E*L) by rw [xx]]
  have le : E*v*x≤L*D*(x+K) := by
    by_contra! hh
    exact (not_lt_of_ge sq) (sq_lt_sq' (by nlinarith [show 0≤L*D*(x+K) by positivity]) hh)
  change E*(E*v-L*D)≤K*x*D
  apply (mul_le_mul_iff_left₀ hl).mp
  nlinarith only [mul_le_mul_of_nonneg_right le hx.le,
    show E*v*x^2=E*v*(E*L) by rw [xx],show L*D*x^2=L*D*(E*L) by rw [xx]]

variable (c : ForwardImmersion)

theorem nodal_log_energy_barrier (hf : c.IsNormalFEF) {T K : ℝ}
    (hT : 0≤T) (hK : 0≤K) (hs : ∀t>T, NodalSliceBound (c.energy t) (c.length t) (c.dissipation t) K) :
    AntitoneOn (fun t => Real.sqrt (c.normalizedProduct t)+(K/2)*Real.log (c.energy t)) (Ici T) := by
  let W := fun t => Real.sqrt (c.normalizedProduct t)+(K/2)*Real.log (c.energy t)
  have sub : Ici T ⊆ Ici 0 := fun _ ht => hT.trans ht
  have hc : ContinuousOn W (Ici T) :=
    (Real.continuous_sqrt.comp_continuousOn (c.normalizedProduct_continuousOn.mono sub)).add
      (continuousOn_const.mul ((c.energy_continuousOn.mono sub).log (fun _ hx => (c.energy_pos (sub hx)).ne')))
  have derivW {t:ℝ} (ht:T<t) : HasDerivAt W
       ((c.energy t*c.lengthRate t-c.length t*c.dissipation t)/(2*Real.sqrt (c.normalizedProduct t))+
        (K/2)*(-c.dissipation t/c.energy t)) t := by
    have hpos := hT.trans_lt ht
    have hn : c.normalizedProduct t ≠ 0 := (mul_pos (c.energy_pos hpos.le) (c.length_pos hpos.le)).ne'
    exact ((c.normalizedProduct_hasDerivAt_normal hf hpos).sqrt hn).add
      (((c.energy_hasDerivAt_normal hf hpos).log (c.energy_pos hpos.le).ne').const_mul (K/2))
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) hc
  · rw [interior_Ici]
    intro t ht
    exact (derivW ht).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro t ht
    rw [(derivW ht).deriv]
    have ht0:0≤t := (hT.trans_lt ht).le
    have he:=c.energy_pos ht0
    have hl:=c.length_pos ht0
    have hx : 0<Real.sqrt (c.normalizedProduct t) := Real.sqrt_pos.mpr (mul_pos he hl)
    have h:=nodal_rate he hl (c.dissipation_nonneg _) hK (c.lengthRate_sq_le ht0) (hs t ht)
    change _≤K*Real.sqrt (c.normalizedProduct t)*c.dissipation t at h
    field_simp [ne_of_gt hx,ne_of_gt he]
    nlinarith only [h]

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.nodal_log_energy_barrier
