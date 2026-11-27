import LengthGrowth.ActualFlow.MulticoverAngleRealization
import LengthGrowth.ActualFlow.MulticoverOutwardLayout

noncomputable section
open Set Function Filter Topology MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.Multicover.Outward

def rotation (t:ℝ):=Complex.exp (Complex.I*(t:ℂ))
theorem rotation_add (x y:ℝ) : rotation (x+y)=rotation x*rotation y:=by
  unfold rotation;rw [←Complex.exp_add];congr 1;push_cast;ring
theorem rotation_turn (m:ℕ) : rotation (2*Real.pi*(m:ℝ))=1:=by
  unfold rotation
  convert Complex.exp_int_mul_two_pi_mul_I (m:ℤ) using 2
  push_cast;ring
theorem rotation_pi : rotation Real.pi= -1:=by unfold rotation;rw [mul_comm];exact Complex.exp_pi_mul_I

namespace Layout
variable {u:ℝ} (a:Layout u)

def angle:=primitive a.curveK

theorem angle_per (full : rotation (a.angle a.period)=1):Periodic (angleTangent a.angle) a.period:=by
  intro s
  have z:=a.periodic.intervalIntegral_add_eq_add 0 s a.smooth.continuous.intervalIntegrable
  rw [zero_add] at z
  change rotation (a.angle (s+a.period))=rotation (a.angle s)
  change a.angle (s+a.period)=a.angle s+a.angle a.period at z
  rw [z,rotation_add,full,mul_one]

theorem swing (half : rotation (a.angle a.half)= -1) {x:ℝ} (hx:x∈Icc 0 a.half) :
    angleTangent a.angle (x+a.half)= -angleTangent a.angle x:=by
  have cc:=a.smooth.continuous
  have after : (∫s in a.half..x+a.half,a.curveK s)=∫s in 0..x,a.curveK s:=by
    have z:=intervalIntegral.integral_comp_add_right (a:=0) (b:=x) (f:=a.curveK) a.half
    rw [zero_add] at z
    rw [←z]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hx.1] at hs
    have one:=a.first_density .turn (show s∈Icc 0 a.half from ⟨hs.1,hs.2.trans hx.2⟩)
    have two:=a.second_density .turn (show s∈Icc 0 (a.period-a.half) from ⟨hs.1,by linarith only [hs.2,hx.2,a.extra]⟩)
    exact two.trans one.symm
  have add:=intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (cc.intervalIntegrable 0 a.half) (cc.intervalIntegrable a.half (x+a.half))
  rw [after] at add
  change a.angle a.half+a.angle x=a.angle (x+a.half) at add
  change rotation (a.angle (x+a.half))= -rotation (a.angle x)
  rw [←add,rotation_add,half];ring

theorem closed (half : rotation (a.angle a.half)= -1) (full : rotation (a.angle a.period)=1) :
    (∫x in 0..a.period,angleTangent a.angle x)=0:=by
  let v:=angleTangent a.angle
  have dθ (s:ℝ):HasDerivAt a.angle (a.curveK s) s:=primitive_derivative a.smooth.continuous s
  have cv : Continuous v:=(angleTangent_smooth (primitive_smooth a.smooth)).continuous
  have z : v 0=1:=by simp [v,angleTangent,angle,primitive]
  have hh : 0≤a.half:=by linarith only [a.two,a.gap]
  have vh : v a.half= -1:=half
  have vh2 : v (2*a.half)=1:=by
    have eq:=a.swing half (x:=a.half) ⟨hh,le_rfl⟩
    change v (a.half+a.half)= -v a.half at eq
    rw [←two_mul,vh,neg_neg] at eq
    exact eq
  have vp : v a.period=1:=full
  have halfint : (∫s in a.half..2*a.half,v s)= -(∫s in 0..a.half,v s):=by
    have tr:=intervalIntegral.integral_comp_add_right (a:=0) (b:=a.half) (f:=v) a.half
    rw [zero_add,←two_mul] at tr
    rw [←tr,←intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hh] at hs
    exact a.swing half hs
  have tail : (∫s in 2*a.half..a.period,v s)=0:=by
    have d (s:ℝ) (hs:s∈uIcc (2*a.half) a.period) :
        HasDerivAt (fun x=> -Complex.I*v x) (v s) s:=by
      rw [uIcc_of_le a.extra] at hs
      have r:=a.second_density .turn (x:=s-a.half) ⟨by linarith only [hs.1,hh],by linarith only [hs.2]⟩
      have t:=late_density (u:=u) .turn (x:=s-a.half) (by linarith only [hs.1,a.gap])
      rw [sub_add_cancel] at r
      have k : a.curveK s=1:=r.trans t
      have dv : HasDerivAt v (v s*(Complex.I*(a.curveK s:ℂ))) s:=((dθ s).ofReal_comp.const_mul Complex.I).cexp
      apply (dv.const_mul (-Complex.I)).congr_deriv
      rw [k,Complex.ofReal_one,mul_one]
      calc -Complex.I*(v s*Complex.I)= -(Complex.I*Complex.I)*v s:=by ring
           _=v s:=by rw [Complex.I_mul_I];ring
    have ft:=intervalIntegral.integral_eq_sub_of_hasDerivAt d (cv.intervalIntegrable (2*a.half) a.period)
    rw [vp,vh2,sub_self] at ft
    exact ft
  change (∫x in 0..a.period,v x)=0
  rw [←intervalIntegral.integral_add_adjacent_intervals (cv.intervalIntegrable 0 (2*a.half)) (cv.intervalIntegrable (2*a.half) a.period),
    ←intervalIntegral.integral_add_adjacent_intervals (cv.intervalIntegrable 0 a.half) (cv.intervalIntegrable a.half (2*a.half)),halfint,tail]
  simp

end Layout
end LengthGrowth.Multicover.Outward
#print axioms LengthGrowth.Multicover.Outward.Layout.closed
