import SolitonClassification.Rotating.IntegerCrossingFaces
import SolitonClassification.RectangleCrossing

namespace SolitonClassification.Rotating.IntegerTarget.CrossingCharts
noncomputable section
open Set Reflected.Rectangle
set_option maxHeartbeats 2500000

private theorem test_neg {x : ℝ} {q e : ℚ} (error : |x-(q:ℝ)|≤(e:ℝ)) (lt : q < -e) : x<0 := by
  have b := (Rat.cast_lt (K:=ℝ)).mpr lt
  push_cast at b
  linarith [(abs_le.mp error).2]
private theorem test_pos {x : ℝ} {q e : ℚ} (error : |x-(q:ℝ)|≤(e:ℝ)) (lt : e<q) : 0<x := by
  have b := (Rat.cast_lt (K:=ℝ)).mpr lt
  linarith [(abs_le.mp error).1]

theorem chart_intersection {c : Parameters} (hc : c∈cube) (k : Fin 2) :
    ∃u∈dom k false, ∃v∈dom k true, gridPosition c u=gridPosition c v := by
  let X := gridPosition c
  let a := lo k false
  let b := lo k true
  let F := fun p:ℝ × ℝ => (projected k false (X p.1) (X p.2),projected k true (X p.1) (X p.2))
  have cont {arm : Bool} : ContinuousOn X (dom k arm) := by
    apply ContinuousOn.prodMk
    · intro u hu
      exact ((grid_rates hc u (dom_grid hu)).1.continuousAt).continuousWithinAt
    · intro u hu
      exact ((grid_rates hc u (dom_grid hu)).2.1.continuousAt).continuousWithinAt
  have fx : ContinuousOn (fun p:ℝ × ℝ => X p.1) (box a (a+8) b (b+8)) := by
    apply cont.comp continuous_fst.continuousOn
    exact fun _ hp => ⟨hp.1.1,hp.2.1⟩
  have fy : ContinuousOn (fun p:ℝ × ℝ => X p.2) (box a (a+8) b (b+8)) := by
    apply cont.comp continuous_snd.continuousOn
    exact fun _ hp => ⟨hp.1.2,hp.2.2⟩
  have cc : ContinuousOn F (box a (a+8) b (b+8)) := by
    dsimp only [F,projected]
    exact (ContinuousOn.add (continuousOn_const.mul (fx.fst.sub fy.fst)) (continuousOn_const.mul (fx.snd.sub fy.snd))).prodMk
      (ContinuousOn.add (continuousOn_const.mul (fx.fst.sub fy.fst)) (continuousOn_const.mul (fx.snd.sub fy.snd)))
  have left (v : ℝ) (hv : v∈Icc b (b+8)) : (F (a,v)).1<0 := by
    obtain ⟨j,V⟩ := varying_close hc (k:=k) (b:=true) hv
    have U := end_close hc k false 0
    simp only [Fin.val_zero,Nat.cast_zero,add_zero] at U
    exact test_neg (projection_error U V (by norm_num)) (numeric_signs k j).1
  have right (v : ℝ) (hv : v∈Icc b (b+8)) : 0<(F (a+8,v)).1 := by
    obtain ⟨j,V⟩ := varying_close hc (k:=k) (b:=true) hv
    have U := end_close hc k false 8
    norm_num only [Fin.reduceFinMk,Nat.cast_ofNat,Fin.val_ofNat] at U
    exact test_pos (projection_error U V (by norm_num)) (numeric_signs k j).2.1
  have bottom (u : ℝ) (hu : u∈Icc a (a+8)) : (F (u,b)).2<0 := by
    obtain ⟨j,U⟩ := varying_close hc (k:=k) (b:=false) hu
    have V := end_close hc k true 0
    simp only [Fin.val_zero,Nat.cast_zero,add_zero] at V
    exact test_neg (projection_error U V (by norm_num)) (numeric_signs k j).2.2.1
  have top (u : ℝ) (hu : u∈Icc a (a+8)) : 0<(F (u,b+8)).2 := by
    obtain ⟨j,U⟩ := varying_close hc (k:=k) (b:=false) hu
    have V := end_close hc k true 8
    norm_num only [Fin.reduceFinMk,Nat.cast_ofNat,Fin.val_ofNat] at V
    exact test_pos (projection_error U V (by norm_num)) (numeric_signs k j).2.2.2
  obtain ⟨p,hp,eq⟩ := zero_in_box a (a+8) b (b+8) (by linarith) (by linarith) F cc left right bottom top
  refine ⟨p.1,⟨hp.1.1,hp.2.1⟩,p.2,⟨hp.1.2,hp.2.2⟩,?_⟩
  have E := congrArg Prod.fst eq
  have G := congrArg Prod.snd eq
  change (coeffX k false:ℝ)*((X p.1).1-(X p.2).1)+(coeffY k false:ℝ)*((X p.1).2-(X p.2).2)=0 at E
  change (coeffX k true:ℝ)*((X p.1).1-(X p.2).1)+(coeffY k true:ℝ)*((X p.1).2-(X p.2).2)=0 at G
  have H : (coeffX k false:ℝ)*(coeffY k true:ℝ)-(coeffY k false:ℝ)*(coeffX k true:ℝ)≠0 := by exact_mod_cast nonsingular k
  apply Prod.ext
  · apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (?_ : _*((X p.1).1-(X p.2).1)=0)).resolve_left H
    linear_combination (coeffY k true:ℝ)*E-(coeffY k false:ℝ)*G
  · apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (?_ : _*((X p.1).2-(X p.2).2)=0)).resolve_left H
    linear_combination (coeffX k false:ℝ)*G-(coeffX k true:ℝ)*E

theorem separate_locations {c : Parameters} (hc : c∈cube) (k : Fin 2) {u : ℝ} (hu : u∈dom k false) :
    (if k=0 then 6 else 11/2)<(gridPosition c u).1 ∧
    (gridPosition c u).1<(if k=0 then 62/10 else 58/10) := by
  obtain ⟨j,K⟩ := varying_close hc hu
  have L := (Rat.cast_lt (K:=ℝ)).mpr (position_ranges k j).1
  have R := (Rat.cast_lt (K:=ℝ)).mpr (position_ranges k j).2
  have B := abs_le.mp K.1
  by_cases hk : k=0
  · simp only [if_pos hk] at L R ⊢
    push_cast at L R
    constructor <;> linarith [B.1,B.2]
  · simp only [if_neg hk] at L R ⊢
    push_cast at L R
    constructor <;> linarith [B.1,B.2]

end
end SolitonClassification.Rotating.IntegerTarget.CrossingCharts
#print axioms SolitonClassification.Rotating.IntegerTarget.CrossingCharts.chart_intersection

