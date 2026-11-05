import Lemniscate.BernoulliGeometry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The reference length is the complete elliptic integral appearing in
the paper, with parameter one half. No spectral or numerical data enter. -/
noncomputable section
namespace Lemniscate
open MeasureTheory

def Khalf : ℝ :=
  ∫ u in (0:ℝ)..Real.pi/2, 1/Real.sqrt (1-(Real.sin u)^2/2)

theorem bernoulli_reference_length :
    (∫ u in (0:ℝ)..(2*Real.pi), ‖bernoulliVelocity u‖)=4*Khalf/Real.sqrt 2 := by
  let v : ℝ → ℝ := fun u => ‖bernoulliVelocity u‖
  have hv : Continuous v :=
    (continuous_iff_continuousAt.mpr
      (fun u => (bernoulli_curve_geometry u).2.1.continuousAt)).norm
  have hper : Function.Periodic v Real.pi := by
    intro u
    change ‖bernoulliVelocity (u+Real.pi)‖=‖bernoulliVelocity u‖
    rw [(bernoulli_curve_geometry (u+Real.pi)).2.2.1,
      (bernoulli_curve_geometry u).2.2.1,Real.sin_add_pi,neg_sq]
  have hreflect (u : ℝ) : v (Real.pi-u)=v u := by
    dsimp only [v]
    rw [(bernoulli_curve_geometry (Real.pi-u)).2.2.1,
      (bernoulli_curve_geometry u).2.2.1,Real.sin_pi_sub]
  have hdouble : (∫ u in (0:ℝ)..(2*Real.pi), v u)=
      (∫ u in (0:ℝ)..Real.pi, v u)+(∫ u in (0:ℝ)..Real.pi, v u) := by
    have hh := hper.intervalIntegral_add_eq_add 0 Real.pi
      (fun a b => hv.intervalIntegrable a b)
    simpa only [zero_add,show Real.pi+Real.pi=2*Real.pi by ring] using hh
  have hreflectIntegral : (∫ u in (0:ℝ)..Real.pi/2, v u)=
      ∫ u in Real.pi/2..Real.pi, v u := by
    have hh := intervalIntegral.integral_comp_sub_left v Real.pi
      (a := 0) (b := Real.pi/2)
    rw [show (fun u => v (Real.pi-u))=v from funext hreflect] at hh
    simpa only [sub_zero,show Real.pi-Real.pi/2=Real.pi/2 by ring] using hh
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hv.intervalIntegrable 0 (Real.pi/2)) (hv.intervalIntegrable (Real.pi/2) Real.pi)
  rw [← hreflectIntegral] at hsum
  have hfull : (∫ u in (0:ℝ)..(2*Real.pi), v u)=
      4*(∫ u in (0:ℝ)..Real.pi/2, v u) := by
    rw [hdouble]
    linarith only [hsum]
  have hroot2 : Real.sqrt (2:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hpoint (u : ℝ) :
      1/Real.sqrt (1-(Real.sin (Real.pi/2-u))^2/2)=Real.sqrt 2*v u := by
    rw [Real.sin_pi_div_two_sub]
    have hden : 1-(Real.cos u)^2/2=(1+(Real.sin u)^2)/2 := by
      nlinarith only [Real.sin_sq_add_cos_sq u]
    rw [hden,Real.sqrt_div (by positivity : (0:ℝ)≤1+(Real.sin u)^2)]
    dsimp only [v]
    rw [(bernoulli_curve_geometry u).2.2.1]
    have hroot : Real.sqrt (1+(Real.sin u)^2)≠0 := ne_of_gt
      (Real.sqrt_pos.mpr (by nlinarith only [sq_nonneg (Real.sin u)]))
    field_simp [hroot,hroot2] <;> ring
  have hK : Khalf=Real.sqrt 2*(∫ u in (0:ℝ)..Real.pi/2, v u) := by
    have hh := intervalIntegral.integral_comp_sub_left
      (fun u => 1/Real.sqrt (1-(Real.sin u)^2/2)) (Real.pi/2)
      (a := 0) (b := Real.pi/2)
    rw [show (fun u => 1/Real.sqrt (1-(Real.sin (Real.pi/2-u))^2/2))=
      (fun u => Real.sqrt 2*v u) from funext hpoint,
      intervalIntegral.integral_const_mul] at hh
    simpa only [sub_self,sub_zero,Khalf] using hh.symm
  change (∫ u in (0:ℝ)..(2*Real.pi), v u)=4*Khalf/Real.sqrt 2
  rw [hfull,hK]
  field_simp [hroot2] <;> ring

end Lemniscate
