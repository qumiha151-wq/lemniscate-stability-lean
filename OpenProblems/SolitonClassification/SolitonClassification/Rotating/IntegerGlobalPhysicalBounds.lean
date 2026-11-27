import SolitonClassification.Rotating.IntegerGlobalNodeTable
import SolitonClassification.Rotating.IntegerGlobalArcBounds
import SolitonClassification.Rotating.IntegerTwoArmImmersion
import Mathlib.Algebra.Order.ToIntervalMod

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
noncomputable section
open Set Metric DyadicReset CrossingCharts
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

private theorem initial_time_error {c : Parameters} (hc : c∈cube) : |c 2-center 2|≤1/10^30 :=
  (norm_le_pi_norm (c-center) 2).trans (show ‖c-center‖≤1/(10:ℝ)^30 from hc)

theorem half_grid_error {c : Parameters} (hc : c∈cube) : |c 2/CrossingCharts.h-4000|≤1/2000 := by
  have eq : c 2/CrossingCharts.h-4000=(c 2-center 2)/CrossingCharts.h := by
    rw [half_step]
    change c 2/CrossingCharts.h-4000=(c 2-4000*CrossingCharts.h)/CrossingCharts.h
    field_simp [h_mem.1.ne']
  rw [eq,abs_div,abs_of_pos h_mem.1]
  exact (div_le_iff₀ h_mem.1).mpr ((initial_time_error hc).trans (by norm_num [CrossingCharts.h,step,Middle.hn,Middle.hd]))

private theorem arm_curvature {n : ℤ} (T : PolynomialTape n 4000)
    (first : T.node 0=initialNode) (stepSmall : |step n|≤1/125) {c : Parameters} (hc : c∈cube)
    {endt η : ℝ} (distT : |endt-4000*step n|≤1/10^30) (hη : η∈unitCell) :
    |wideFlow (η*endt,shootingInitial phase c) 0|≤10 := by
  let a := shootingInitial phase c
  obtain ⟨i,hi,t,ht,he⟩ := covered_cell 4000 (by decide) (4000*η) (by linarith [hη.1])
    (by norm_num; linarith [hη.2])
  have p := (prefix_physical T (by decide) (by decide) stepSmall first hc i hi t ht).2
  have st : ((i:ℝ)+t)*step n=η*(4000*step n) := by rw [←he]; ring
  rw [st] at p
  have dt : |η*endt-η*(4000*step n)|≤1/10^30 := by
    rw [←mul_sub,abs_mul,abs_of_nonneg hη.1]
    exact (mul_le_mul hη.2 distT (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have tm := lipschitzWith_iff_norm_sub_le.mp (wide_time_lip a) (η*endt) (η*(4000*step n))
  rw [Real.norm_eq_abs] at tm
  norm_num only [NNReal.coe_ofNat] at tm
  have dis : ‖wideFlow (η*endt,a)-path (T.data i) d t‖≤1 :=
    (norm_sub_le_norm_sub_add_norm_sub _ (wideFlow (η*(4000*step n),a)) _).trans (by dsimp [a] at *; linarith)
  have inner := (lift_inner (T.small i hi) ht).1 0 (by decide)
  change |path (T.data i) d t 0|≤9 at inner
  have diff := (coordinate_bound (wideFlow (η*endt,a)-path (T.data i) d t) 0).trans dis
  change |wideFlow (η*endt,a) 0-path (T.data i) d t 0|≤1 at diff
  have tri := abs_add_le (wideFlow (η*endt,a) 0-path (T.data i) d t 0) (path (T.data i) d t 0)
  rw [sub_add_cancel] at tri
  change |wideFlow (η*endt,a) 0|≤10
  linarith

private theorem physical_periodic_k {b L : ℝ} (I : WindingOneImmersion b L) : Function.Periodic I.k L := by
  intro s
  have sh : HasDerivAt (fun u=>I.theta (u+L)) (I.k (s+L)) s := by
    exact (I.angleDerivative (s+L)).comp_add_const s L
  have un : HasDerivAt (fun u=>I.theta u-2*Real.pi) (I.k s) s := (I.angleDerivative s).sub_const _
  rw [funext I.turning] at sh
  exact sh.unique un

theorem bounds_of_physical_trace (c : Parameters) (hc : c∈cube)
    (I : WindingOneImmersion (c 4) (2*c 2))
    (trace : ∀s∈Icc (-(c 2)) (c 2), (I.x s,I.y s)=segmentPosition c s ∧
      I.k s=wideFlow (s,shootingInitial phase c) 0) :
    |c 2/CrossingCharts.h-4000|≤1/2000 ∧ NodeBounds I ∧ (∀w,|I.k w|≤10) ∧
    (∀v, -(c 2/CrossingCharts.h)≤v → v≤c 2/CrossingCharts.h → atGrid I v=gridPosition c v) := by
  have half := half_grid_error hc
  have range (v : ℝ) (lo : -(c 2/CrossingCharts.h)≤v) (hi : v≤c 2/CrossingCharts.h) : v*CrossingCharts.h∈Icc (-(c 2)) (c 2) := by
    have u := (le_div_iff₀ h_mem.1).mp hi
    rw [←neg_div] at lo
    exact ⟨(div_le_iff₀ h_mem.1).mp lo,u⟩
  have grids (v : ℝ) (lo : -(c 2/CrossingCharts.h)≤v) (hi : v≤c 2/CrossingCharts.h) : atGrid I v=gridPosition c v :=
    (trace (v*CrossingCharts.h) (range v lo hi)).1
  refine ⟨half,?_,?_,grids⟩
  · intro i hi axis
    have bound : |((refPoint i).index:ℝ)|≤3999 := by exact_mod_cast reference_index_bound i hi
    have inside := grids (refPoint i).index (by linarith only [(abs_le.mp bound).1,(abs_le.mp half).1])
      (by linarith only [(abs_le.mp bound).2,(abs_le.mp half).1])
    rw [inside]
    have vv := reference_position_errors c hc i hi
    cases axis
    · exact vv.1
    · exact vv.2
  · have pos : 0<c 2 := by
      have hp : 0<c 2/CrossingCharts.h := by linarith only [(abs_le.mp half).1]
      exact (div_pos_iff.mp hp).elim (fun z=>z.1) (fun z=>(not_lt_of_ge h_mem.1.le z.2).elim)
    have cap (s : ℝ) (hs : s∈Icc (-(c 2)) (c 2)) : |I.k s|≤10 := by
      rw [(trace s hs).2]
      by_cases h0 : 0≤s
      · have eta : s/c 2∈unitCell := ⟨div_nonneg h0 pos.le,(div_le_one pos).mpr hs.2⟩
        have tau : |c 2-4000*step Middle.hn|≤1/10^30 := by rw [←half_step]; exact initial_time_error hc
        have z := arm_curvature CompletePlus.tape ((CompletePlus.range 0 (by decide)).1.trans rfl)
          (signedHalfSteps true) hc tau eta
        simpa only [div_mul_cancel₀ _ pos.ne'] using z
      · have eta : (-s)/c 2∈unitCell := ⟨div_nonneg (by linarith) pos.le,(div_le_one pos).mpr (by linarith [hs.1])⟩
        have tau : |-(c 2)-4000*step (-Middle.hn)|≤1/10^30 := by
          rw [←minus_half_step,show -(c 2)-(-(center 2))= -(c 2-center 2) by ring,abs_neg]
          exact initial_time_error hc
        have z := arm_curvature CompleteMinus.tape ((CompleteMinus.range 0 (by decide)).1.trans rfl)
          (signedHalfSteps false) hc tau eta
        simpa only [mul_neg,div_mul_cancel₀ _ pos.ne',neg_neg] using z
    intro w
    have pp : 0<2*c 2 := by linarith
    let v := toIcoMod pp (-(c 2)) w
    have iv := toIcoMod_mem_Ico pp (-(c 2)) w
    have hv : v∈Icc (-(c 2)) (c 2) := ⟨iv.1,by dsimp only [v]; linarith only [iv.2]⟩
    have shift := (physical_periodic_k I).zsmul (toIcoDiv pp (-(c 2)) w) v
    rw [show v+toIcoDiv pp (-(c 2)) w • (2*c 2)=w from toIcoMod_add_toIcoDiv_zsmul pp _ _] at shift
    rw [shift]
    exact cap v hv

end
end SolitonClassification.Rotating.IntegerTarget.GlobalCount
#print axioms SolitonClassification.Rotating.IntegerTarget.GlobalCount.bounds_of_physical_trace
