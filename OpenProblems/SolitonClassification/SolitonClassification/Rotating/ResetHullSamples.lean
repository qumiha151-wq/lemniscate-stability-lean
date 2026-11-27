import SolitonClassification.Rotating.ResetHullPlus
import SolitonClassification.Rotating.ResetHullMinus
import SolitonClassification.Rotating.ResetHullFrames
import SolitonClassification.Rotating.ResetThreePointHull

namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
open Set DyadicReset
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000

def segmentPosition (c : Parameters) (s : ℝ) := framePosition (wideFlow (s,shootingInitial phase c))

def lowerTime := 3193*step (-Middle.hn)
def upperTime := 636*step Middle.hn

theorem sample_times : lowerTime<0 ∧ 0<upperTime ∧ -25<lowerTime ∧ upperTime<5 := by
  norm_num [lowerTime,upperTime,step,Middle.hn,Middle.hd]

theorem initial_sample {c : Parameters} (hc : c∈cube) :
    (segmentPosition c 0).1∈Icc (-(13/100)) (-(8/100)) ∧
    (segmentPosition c 0).2∈Icc (13/100) (19/100) := by
  let z := wideFlow ((((0:ℕ):ℝ)*step Middle.hn),shootingInitial phase c)
  have row := HullPlus.node_at 0 (by decide)
  have clos (j : Fin 6) : |z j-(rationalState (GridPlus.atNode 0) j:ℝ)|≤5/10^26 := by
    rw [←row]
    exact prefix_node_coordinates HullPlus.tape (by decide) (by decide) (signedHalfSteps true)
      (show HullPlus.tape.node 0=initialNode from (HullPlus.node_at 0 (by decide)).trans rfl)
      hc 0 (by decide : 0<640) j
  have p := observed_coordinate (l:=(157/1000:ℚ)) (u:=(159/1000:ℚ)) (clos 2)
    (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg,Rat.cast_one] at p
  have q := observed_coordinate (l:=(-107/1000:ℚ)) (u:=(-104/1000:ℚ)) (clos 3)
    (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg,Rat.cast_one] at q
  have a := observed_coordinate (l:=(-1/1000:ℚ)) (u:=(1/1000:ℚ)) (clos 5)
    (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg,Rat.cast_one] at a
  have shift : |z 5-0|≤1/250 := abs_le.mpr ⟨by linarith [a.1],by linarith [a.2]⟩
  have size : |z 2|+|z 3|≤5 := by
    rw [abs_of_nonneg (by linarith [p.1] : 0≤z 2),abs_of_nonpos (by linarith [q.2] : z 3≤0)]
    linarith [p.2,q.1,q.2]
  have f := frame_bound z Real.cos_zero Real.sin_zero shift size
  have xx := abs_le.mp f.1
  have yy := abs_le.mp f.2
  have ident : segmentPosition c 0=framePosition z := by simp [segmentPosition,z]
  rw [ident]
  exact ⟨⟨by linarith [xx.1,q.1,q.2],by linarith [xx.2,q.1,q.2]⟩,
    ⟨by linarith [yy.1,p.1,p.2],by linarith [yy.2,p.1,p.2]⟩⟩

theorem right_sample {c : Parameters} (hc : c∈cube) :
    (segmentPosition c upperTime).1∈Icc (2) (22/10) ∧
    (segmentPosition c upperTime).2∈Icc (6/10) (73/100) := by
  let z := wideFlow (((636:ℝ)*step Middle.hn),shootingInitial phase c)
  have row := HullPlus.node_at 636 (by decide)
  have clos (j : Fin 6) : |z j-(rationalState (GridPlus.atNode 636) j:ℝ)|≤5/10^26 := by
    rw [←row]
    exact prefix_node_coordinates HullPlus.tape (by decide) (by decide) (signedHalfSteps true)
      (show HullPlus.tape.node 0=initialNode from (HullPlus.node_at 0 (by decide)).trans rfl)
      hc 636 (by decide : 636<640) j
  have p := observed_coordinate (l:=(661/1000:ℚ)) (u:=(664/1000:ℚ)) (clos 2)
    (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg,Rat.cast_one] at p
  have q := observed_coordinate (l:=(2089/1000:ℚ)) (u:=(2092/1000:ℚ)) (clos 3)
    (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg,Rat.cast_one] at q
  have a := observed_coordinate (l:=(-3/1000:ℚ)) (u:=(-1/1000:ℚ)) (clos 5)
    (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg,Rat.cast_one] at a
  have shift : |z 5-0|≤1/250 := abs_le.mpr ⟨by linarith [a.1],by linarith [a.2]⟩
  have size : |z 2|+|z 3|≤5 := by
    rw [abs_of_nonneg (by linarith [p.1] : 0≤z 2),abs_of_nonneg (by linarith [q.1] : 0≤z 3)]
    linarith [p.2,q.1,q.2]
  have f := frame_bound z Real.cos_zero Real.sin_zero shift size
  have xx := abs_le.mp f.1
  have yy := abs_le.mp f.2
  have ident : segmentPosition c upperTime=framePosition z := by rfl
  rw [ident]
  exact ⟨⟨by linarith [xx.1,q.1,q.2],by linarith [xx.2,q.1,q.2]⟩,
    ⟨by linarith [yy.1,p.1,p.2],by linarith [yy.2,p.1,p.2]⟩⟩

theorem bottom_sample {c : Parameters} (hc : c∈cube) :
    (segmentPosition c lowerTime).1∈Icc (-(27/10)) (-(25/10)) ∧
    (segmentPosition c lowerTime).2∈Icc (-(21/10)) (-(19/10)) := by
  let z := wideFlow (((3193:ℝ)*step (-Middle.hn)),shootingInitial phase c)
  have row := HullMinus.node_at 3193 (by decide)
  have clos (j : Fin 6) : |z j-(rationalState (GridMinus.atNode 3193) j:ℝ)|≤5/10^26 := by
    rw [←row]
    exact prefix_node_coordinates HullMinus.tape (by decide) (by decide) (signedHalfSteps false)
      (show HullMinus.tape.node 0=initialNode from (HullMinus.node_at 0 (by decide)).trans rfl)
      hc 3193 (by decide : 3193<3200) j
  have p := observed_coordinate (l:=(2036/1000:ℚ)) (u:=(2039/1000:ℚ)) (clos 2)
    (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg,Rat.cast_one] at p
  have q := observed_coordinate (l:=(2609/1000:ℚ)) (u:=(2612/1000:ℚ)) (clos 3)
    (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg,Rat.cast_one] at q
  have a := observed_coordinate (l:=(3140/1000:ℚ)) (u:=(3142/1000:ℚ)) (clos 5)
    (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg,Rat.cast_one] at a
  have shift : |z 5-Real.pi|≤1/250 := abs_le.mpr ⟨by linarith [a.1,Real.pi_lt_d4],by linarith [a.2,Real.pi_gt_d4]⟩
  have size : |z 2|+|z 3|≤5 := by
    rw [abs_of_nonneg (by linarith [p.1] : 0≤z 2),abs_of_nonneg (by linarith [q.1] : 0≤z 3)]
    linarith [p.2,q.1,q.2]
  have f := frame_bound z Real.cos_pi Real.sin_pi shift size
  have xx := abs_le.mp f.1
  have yy := abs_le.mp f.2
  have ident : segmentPosition c lowerTime=framePosition z := by rfl
  rw [ident]
  exact ⟨⟨by linarith [xx.1,q.1,q.2],by linarith [xx.2,q.1,q.2]⟩,
    ⟨by linarith [yy.1,p.1,p.2],by linarith [yy.2,p.1,p.2]⟩⟩

/-- Every nearby shooting parameter has a physical arc enclosing the same
square about its similarity center, before imposing the closing condition. -/
theorem square_in_shooting_arc {c : Parameters} (hc : c∈cube) :
    ∀z : ℝ × ℝ, |z.1|≤1/20 → |z.2|≤1/20 →
      z∈convexHull ℝ (segmentPosition c '' Icc lowerTime upperTime) := by
  have lt := sample_times.1
  have rt := sample_times.2.1
  have A := initial_sample hc
  have B := bottom_sample hc
  have R := right_sample hc
  apply fixed_square_of_three_boxes (S:=segmentPosition c '' Icc lowerTime upperTime)
    (a:=segmentPosition c 0) (b:=segmentPosition c lowerTime) (r:=segmentPosition c upperTime)
    ⟨0,⟨lt.le,rt.le⟩,rfl⟩ ⟨lowerTime,⟨le_rfl,(lt.trans rt).le⟩,rfl⟩
    ⟨upperTime,⟨(lt.trans rt).le,le_rfl⟩,rfl⟩ A.1 A.2 B.1 B.2 R.1 R.2

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.square_in_shooting_arc
