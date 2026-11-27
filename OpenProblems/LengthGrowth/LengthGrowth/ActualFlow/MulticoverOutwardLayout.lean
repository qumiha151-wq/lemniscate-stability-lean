import LengthGrowth.ActualFlow.MulticoverOutwardBlock
import LengthGrowth.ActualFlow.MulticoverOutwardPeriod

noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace LengthGrowth.Multicover.Outward

structure Layout (u:ℝ) where
  half : ℝ
  period : ℝ
  two : 2≤u
  gap : u+3≤half
  extra : 2*half≤period

namespace Layout
variable {u:ℝ} (a:Layout u)

theorem hp : 1<a.period:=by linarith only [a.two,a.gap,a.extra]

def raw (s:ℝ):=block u s+block u (s-a.half)-1
def curveK:=repeatCurve a.period (by linarith only [a.hp]) a.raw

private theorem leftFlat {x:ℝ} (h:x≤1/4) : block u x=1:=by simp [block,cutoff_zero h]
private theorem rightFlat {x:ℝ} (h:u+2-1/4≤x) : block u x=1:=by
  simp [block,cutoff_zero (show u+2-x≤1/4 by linarith)]

theorem raw_flat : (∀x,x≤1/4→a.raw x=1) ∧ (∀x,a.period-1/4≤x→a.raw x=1):=by
  constructor
  · intro x hx
    simp [raw,leftFlat hx,leftFlat (show x-a.half≤1/4 by linarith only [hx,a.gap,a.two])]
  · intro x hx
    simp [raw,rightFlat (show u+2-1/4≤x by linarith only [hx,a.gap,a.extra,a.two]),
      rightFlat (show u+2-1/4≤x-a.half by linarith only [hx,a.gap,a.extra])]

theorem smooth : ContDiff ℝ ∞ a.curveK:=by
  apply repeat_smooth a.hp a.raw _ a.raw_flat
  have sm:ContDiff ℝ ∞ (block u):=block_smooth.comp (show ContDiff ℝ ∞ (fun s:ℝ=>(u,s)) by fun_prop)
  exact (sm.add (sm.comp (contDiff_id.sub contDiff_const))).sub contDiff_const

theorem periodic : Function.Periodic a.curveK a.period:=repeat_periodic a.period (by linarith only [a.hp]) a.raw 

theorem first_density (i:Moment) {x:ℝ} (hx:x∈Icc 0 a.half) : density i a.curveK x=density i (block u) x:=by
  apply density_congr
  apply (repeat_agrees a.hp a.raw a.raw_flat (show x∈Icc 0 a.period from ⟨hx.1,by linarith only [hx.2,a.extra,a.gap,a.two]⟩)).trans
  filter_upwards [gt_mem_nhds (show x<a.half+1/4 by linarith only [hx.2])] with s hs
  simp [raw,leftFlat (show s-a.half≤1/4 by linarith)]

theorem second_density (i:Moment) {x:ℝ} (hx:x∈Icc 0 (a.period-a.half)) :
    density i a.curveK (x+a.half)=density i (block u) x:=by
  have mem : x+a.half∈Icc 0 a.period:=⟨by linarith only [hx.1,a.gap,a.two],by linarith only [hx.2]⟩
  unfold curveK
  rw [density_congr i (repeat_agrees a.hp a.raw a.raw_flat mem),←density_shift]
  apply density_congr
  filter_upwards [lt_mem_nhds (show u+2-1/4-a.half<x by linarith only [a.gap,hx.1])] with s hs
  simp [raw,rightFlat (show u+2-1/4≤s+a.half by linarith)]

def circleMoment (i:Moment):=i.apply 1 (1/2)

theorem late_density (i:Moment) {x:ℝ} (hx:u+2≤x) : density i (block u) x=circleMoment i:=by
  have eq : block u=ᶠ[𝓝 x] fun _=>1:=by
    filter_upwards [lt_mem_nhds (show u+2-1/4<x by linarith)] with s hs
    exact rightFlat hs.le
  rw [density_congr i eq]
  simp [density,circleMoment,deriv_const]

private theorem integral_until (i:Moment) {b:ℝ} (hb:u+2≤b) :
    (∫s in 0..b,density i (block u) s)=blockIntegral i u+(b-(u+2))*circleMoment i:=by
  have cc : Continuous (density i (block u)):=(joint_density block_smooth i).comp
    (show Continuous (fun s:ℝ=>(u,s)) by fun_prop)
  rw [←intervalIntegral.integral_add_adjacent_intervals (cc.intervalIntegrable 0 (u+2)) (cc.intervalIntegrable (u+2) b)]
  congr 1
  calc
    _=(∫_ in (u+2)..b,circleMoment i):=by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hb] at hs
      exact late_density i hs.1
    _=_:=by simp [smul_eq_mul]

theorem half_integral (i:Moment) : (∫s in 0..a.half,density i a.curveK s)=blockIntegral i u+(a.half-(u+2))*circleMoment i:=by
  rw [←integral_until i (by linarith only [a.gap] : u+2≤a.half)]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (by linarith only [a.two,a.gap])] at hs
  exact a.first_density i hs

theorem full_integral (i:Moment) : (∫s in 0..a.period,density i a.curveK s)=2*blockIntegral i u+(a.period-2*(u+2))*circleMoment i:=by
  have continuous_density (k:ℝ→ℝ) (sm:ContDiff ℝ ∞ k) : Continuous (density i k):=by
    have k0:=sm.continuous
    have k2:=(contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp sm).2).2.continuous
    change Continuous (fun s=>density i k s)
    cases i <;> simp only [density,Moment.apply] <;> fun_prop
  have cs:=continuous_density a.curveK a.smooth
  have second : (∫s in a.half..a.period,density i a.curveK s)=
      ∫s in 0..(a.period-a.half),density i (block u) s:=by
    have tr:=intervalIntegral.integral_comp_add_right (a:=0) (b:=a.period-a.half) (f:=density i a.curveK) a.half
    rw [zero_add,sub_add_cancel] at tr
    rw [←tr]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by linarith only [a.extra,a.gap,a.two])] at hs
    exact a.second_density i hs
  have whole:=intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (cs.intervalIntegrable 0 a.half) (cs.intervalIntegrable a.half a.period)
  rw [a.half_integral,second,integral_until i (by linarith only [a.gap,a.extra])] at whole
  rw [←whole]
  ring

end Layout
end LengthGrowth.Multicover.Outward
#print axioms LengthGrowth.Multicover.Outward.Layout.full_integral
