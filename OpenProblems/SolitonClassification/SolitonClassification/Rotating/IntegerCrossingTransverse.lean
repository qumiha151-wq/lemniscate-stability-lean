import SolitonClassification.Rotating.IntegerCrossingFaces

namespace SolitonClassification.Rotating.IntegerTarget.CrossingCharts
noncomputable section
open Set
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def directionDet (k : Fin 2) (i j : Fin 9) : ℚ :=
  sv (loc k true j) 11 * cv (loc k false i) 11 -
    cv (loc k true j) 11 * sv (loc k false i) 11

theorem discrete_transversality : ∀k:Fin 2, ∀i j:Fin 9, (21/50:ℚ)< |directionDet k i j| := by
  decide +kernel

private theorem component_product {a b c d : ℝ} (a1 : |a|≤1) (d1 : |d|≤1)
    (ac : |a-c|≤101/10^6) (bd : |b-d|≤101/10^6) :
    |a*b-c*d|≤202/10^6 := by
  rw [show a*b-c*d=a*(b-d)+(a-c)*d by ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul]
  linarith [mul_le_mul a1 bd (abs_nonneg _) (by norm_num : (0:ℝ)≤1),
    mul_le_mul ac d1 (abs_nonneg _) (by norm_num : (0:ℝ)≤101/10^6)]

private theorem nearby_angle {c : Parameters} (hc : c∈cube) {k : Fin 2} {b : Bool} {x : ℝ}
    (hx : x∈dom k b) :
    ∃j:Fin 9, |gridAngle c x-stateAt c (idx k b j) 5|≤8/100 := by
  obtain ⟨j,hj⟩ := nearest hx
  let i := idx k b j
  let a : ℝ := (sample i).index
  have sb := (basic i).1
  have ha : a∈Icc 0 4000 := ⟨Nat.cast_nonneg _,by dsimp only [a]; exact_mod_cast sb.le⟩
  have L := (grid_lipschitz hc ha (dom_grid hx)).2.2
  have one : |x-a|≤1 := hj
  have d := mul_le_mul_of_nonneg_left one (show 0≤10*h from mul_nonneg (by norm_num) h_mem.1.le)
  refine ⟨j,?_⟩
  change |gridAngle c x-gridAngle c a|≤8/100
  linarith [h_mem.2]

/-- Every pair of arclengths in the two chart windows has transverse
unit tangents, uniformly over the entire closing cube. -/
theorem crossing_angles_transverse {c : Parameters} (hc : c∈cube) {k : Fin 2} {u v : ℝ}
    (hu : u∈dom k false) (hv : v∈dom k true) :
    1/4< |Real.sin (gridAngle c v-gridAngle c u)| := by
  obtain ⟨i,ai⟩ := nearby_angle hc hu
  obtain ⟨j,aj⟩ := nearby_angle hc hv
  let I := idx k false i
  let J := idx k true j
  let A := stateAt c I 5
  let B := stateAt c J 5
  have ui := direction_errors c hc I
  have vj := direction_errors c hc J
  have nc := (angles I).unitC 11 (by decide)
  have ns := (angles I).unitS 11 (by decide)
  change |cv (sample I) 11|≤1 at nc
  change |sv (sample I) 11|≤1 at ns
  have CR := (Rat.cast_le (K:=ℝ)).mpr nc
  have SR := (Rat.cast_le (K:=ℝ)).mpr ns
  push_cast at CR SR
  have p₁ := component_product (Real.abs_sin_le_one B) CR vj.2 ui.1
  have p₂ := component_product (Real.abs_cos_le_one B) SR vj.1 ui.2
  have err : |Real.sin (B-A)-(directionDet k i j:ℝ)|≤404/10^6 := by
    rw [Real.sin_sub]
    unfold directionDet
    push_cast
    change |Real.sin B*Real.cos A-Real.cos B*Real.sin A-
      ((sv (sample J) 11:ℝ)*(cv (sample I) 11:ℝ)-(cv (sample J) 11:ℝ)*(sv (sample I) 11:ℝ))|≤_
    rw [show ∀a b c d:ℝ,a-b-(c-d)=(a-c)-(b-d) by intros;ring]
    exact (abs_sub _ _).trans (by linarith only [p₁,p₂])
  have low := (Rat.cast_lt (K:=ℝ)).mpr (discrete_transversality k i j)
  push_cast at low
  have near : |(gridAngle c v-gridAngle c u)-(B-A)|≤16/100 := by
    rw [show (gridAngle c v-gridAngle c u)-(B-A)=(gridAngle c v-B)-(gridAngle c u-A) by ring]
    exact (abs_sub _ _).trans (by linarith only [aj,ai])
  have close := (Real.abs_sin_sub_sin_le _ _).trans near
  have tri (a b : ℝ) : |b|≤|a|+|a-b| := by
    have hh := abs_sub a (a-b)
    rwa [sub_sub_cancel] at hh
  linarith only [tri (Real.sin (B-A)) (directionDet k i j:ℝ),
    tri (Real.sin (gridAngle c v-gridAngle c u)) (Real.sin (B-A)),close,err,low]

end
end SolitonClassification.Rotating.IntegerTarget.CrossingCharts
#print axioms SolitonClassification.Rotating.IntegerTarget.CrossingCharts.crossing_angles_transverse
