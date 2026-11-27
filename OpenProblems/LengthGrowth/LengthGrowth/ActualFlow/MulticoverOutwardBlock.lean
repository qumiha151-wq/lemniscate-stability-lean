import LengthGrowth.ActualFlow.MulticoverOutwardFields
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.Multicover.Outward

def blockIntegral (i:Moment) (u:ℝ):=∫s in 0..u+2,density i (block u) s

def blockIntegrals (u:ℝ) : Integrals:=
  ⟨blockIntegral .turn u,blockIntegral .square u,blockIntegral .rate u,blockIntegral .diss u⟩

theorem blockIntegral_continuous (i:Moment):Continuous (blockIntegral i):=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (joint_density block_smooth i) (by fun_prop)

theorem block_defect_continuous (m:ℝ):Continuous (fun u=>defect m u (blockIntegrals u)):=by
  unfold defect blockIntegrals
  have t:=blockIntegral_continuous .turn
  have b:=blockIntegral_continuous .square
  fun_prop

private theorem middle_mean (i:Moment):∃B:ℝ,∀u,2≤u →
    |(∫s in 1..(u+1),density i (block u) s)-u*i.val waveMoments|≤B:=by
  let a : Fn:=match i with
    | .turn=>wave | .square=>wave^2 | .rate=>wave*waveForce | .diss=>waveForce^2
  have h : Mean a (i.val waveMoments):=by cases i <;>
    first | exact wave_means.1 | exact wave_means.2.1 | exact wave_means.2.2.1 | exact wave_means.2.2.2
  obtain ⟨B,hB⟩:=h
  refine ⟨B,fun u hu=>?_⟩
  have eq : (∫s in 1..(u+1),density i (block u) s)=∫s in 1..(u+1),a s:=by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by linarith : 1≤u+1)] at hs
    rw [middle_density i hs]
    unfold density
    rw [wave_second_force]
    cases i <;> rfl
  rw [eq]
  simpa only [add_sub_cancel_right] using hB 1 (u+1)

theorem blockIntegral_error (i:Moment) : ∃B:ℝ,∀u,2≤u →
    |blockIntegral i u-u*i.val waveMoments|≤B:=by
  obtain ⟨B,_,hB⟩:=uniform_ends i
  obtain ⟨C,hC⟩:=middle_mean i
  refine ⟨B+B+C,fun u hu=>?_⟩
  let f:=density i (block u)
  have cf : Continuous f:=(joint_density block_smooth i).comp
    (show Continuous (fun s:ℝ=>(u,s)) by fun_prop)
  have edge {x:ℝ} (h:∀s∈Icc x (x+1),|f s|≤B) : |∫s in x..x+1,f s|≤B:=by
    have g:=intervalIntegral.norm_integral_le_of_norm_le_const (a:=x) (b:=x+1) (f:=f) (C:=B)
      (by intro s hs;rw [uIoc_of_le (by linarith : x≤x+1)] at hs;exact h s ⟨hs.1.le,hs.2⟩)
    simpa [Real.norm_eq_abs] using g
  have l:=edge (x:=0) (by simpa using (hB u hu).1)
  have r:=edge (x:=u+1) (by simpa only [show u+1+1=u+2 by ring] using (hB u hu).2)
  rw [zero_add] at l
  rw [show u+1+1=u+2 by ring] at r
  have sum := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (cf.intervalIntegrable 0 1) (cf.intervalIntegrable 1 (u+1))
  have sum2 := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (cf.intervalIntegrable 0 (u+1)) (cf.intervalIntegrable (u+1) (u+2))
  change |(∫s in 0..u+2,f s)-u*i.val waveMoments|≤_
  rw [←sum2,←sum]
  have mid:=hC u hu
  change |(∫s in 1..u+1,f s)-u*i.val waveMoments|≤C at mid
  exact abs_le.mpr ⟨by linarith only [(abs_le.mp l).1,(abs_le.mp r).1,(abs_le.mp mid).1],
    by linarith only [(abs_le.mp l).2,(abs_le.mp r).2,(abs_le.mp mid).2]⟩

theorem block_uniform : ∃R:ℝ,1≤R ∧ ∀u,512*R≤u→Errors R u (blockIntegrals u):=by
  obtain ⟨a,ha⟩:=blockIntegral_error .turn
  obtain ⟨b,hb⟩:=blockIntegral_error .square
  obtain ⟨j,hj⟩:=blockIntegral_error .rate
  obtain ⟨d,hd⟩:=blockIntegral_error .diss
  let R:=max 1 (max (max a b) (max j d))
  have high : 1≤R:=le_max_left .. 
  have lower : max (max a b) (max j d)≤R:=le_max_right ..
  refine ⟨R,high,fun u hu=>?_⟩
  have h : 2≤u:=by linarith only [hu,high]
  exact ⟨(by simpa [blockIntegrals,Moment.val,waveMoments] using (ha u h).trans ((le_max_left a b).trans ((le_max_left ..).trans lower))),
    (by simpa [blockIntegrals,Moment.val,waveMoments,mul_comm] using (hb u h).trans ((le_max_right a b).trans ((le_max_left ..).trans lower))),
    (by simpa [blockIntegrals,Moment.val,waveMoments,mul_comm] using (hj u h).trans ((le_max_left j d).trans ((le_max_right ..).trans lower))),
    (by simpa [blockIntegrals,Moment.val,waveMoments,mul_comm] using (hd u h).trans ((le_max_right j d).trans ((le_max_right ..).trans lower)))⟩

end LengthGrowth.Multicover.Outward
#print axioms LengthGrowth.Multicover.Outward.block_uniform
