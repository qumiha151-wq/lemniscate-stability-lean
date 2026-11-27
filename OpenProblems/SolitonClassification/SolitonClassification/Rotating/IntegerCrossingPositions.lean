import SolitonClassification.Rotating.IntegerCrossingSamples
import SolitonClassification.Rotating.ResetHullSamples

namespace SolitonClassification.Rotating.IntegerTarget.CrossingCharts
noncomputable section
open Set DyadicReset
set_option maxHeartbeats 2000000

def timeAt (i : Fin 36) := ((sample i).index:ℝ)*step Middle.hn
def stateAt (c : Parameters) (i : Fin 36) := wideFlow (timeAt i,shootingInitial phase c)

private theorem observed (c : Parameters) (hc : c∈cube) (i : Fin 36) (j : Fin 6) (q : ℚ)
    (bound : |rationalState (GridPlus.atNode (sample i).index) j-q|≤1/10^8) :
    |stateAt c i j-(q:ℝ)|≤1/10^7 := by
  have idx := (basic i).1
  have first : CompletePlus.tape.node 0=initialNode := (CompletePlus.range 0 (by decide)).1.trans rfl
  have h := prefix_node_coordinates CompletePlus.tape (by decide) (by decide) (signedHalfSteps true) first hc (sample i).index idx j
  have node : CompletePlus.tape.node (sample i).index=GridPlus.atNode (sample i).index :=
    (CompletePlus.range _ idx).1
  rw [node] at h
  have b := (Rat.cast_le (K:=ℝ)).mpr bound
  push_cast at b
  apply (abs_sub_le _ (rationalState (GridPlus.atNode (sample i).index) j:ℝ) _).trans
  change |stateAt c i j-_|+_≤_
  change |stateAt c i j-_|≤_ at h
  linarith only [h,b]

theorem direction_errors (c : Parameters) (hc : c∈cube) (i : Fin 36) :
    |Real.cos (stateAt c i 5)-(cv (sample i) 11:ℝ)|≤101/10^6 ∧
    |Real.sin (stateAt c i 5)-(sv (sample i) 11:ℝ)|≤101/10^6 := by
  obtain ⟨_,_,_,_,_,th,_⟩ := basic i
  have z := observed c hc i 5 _ th
  have a := double_angles_sound (angles i)
  have cc := (Real.abs_cos_sub_cos_le _ _).trans z
  have ss := (Real.abs_sin_sub_sin_le _ _).trans z
  change |Real.cos _-(cv (sample i) 11:ℝ)|≤_ ∧ |Real.sin _-(sv (sample i) 11:ℝ)|≤_ at a
  exact ⟨(abs_sub_le _ (Real.cos ((sample i).theta:ℝ)) _).trans (by linarith [a.1]),
    (abs_sub_le _ (Real.sin ((sample i).theta:ℝ)) _).trans (by linarith [a.2])⟩

private theorem product_bound {x a v b : ℝ} (xa : |x-a|≤1/10^7) (unit : |v|≤1)
    (vb : |v-b|≤101/10^6) : |x*v-a*b|≤1/10^7+|a| * (101/10^6) := by
  rw [show x*v-a*b=(x-a)*v+a*(v-b) by ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul]
  have A := mul_le_mul xa unit (abs_nonneg _) (by norm_num : (0:ℝ)≤1/10^7)
  have B := mul_le_mul_of_nonneg_left vb (abs_nonneg a)
  linarith

theorem position_errors (c : Parameters) (hc : c∈cube) (i : Fin 36) :
    |(segmentPosition c (timeAt i)).1-((sample i).x:ℝ)|≤1/800 ∧
    |(segmentPosition c (timeAt i)).2-((sample i).y:ℝ)|≤1/800 := by
  let r:=sample i
  let z:=stateAt c i
  obtain ⟨_,_,mag,p,q,_,_,_,x,y⟩ := basic i
  have pe := observed c hc i 2 _ p
  have qe := observed c hc i 3 _ q
  obtain ⟨ce,se⟩ := direction_errors c hc i
  have A := product_bound qe (Real.abs_cos_le_one _) ce
  have B := product_bound pe (Real.abs_sin_le_one _) se
  have C := product_bound qe (Real.abs_sin_le_one _) se
  have D := product_bound pe (Real.abs_cos_le_one _) ce
  have m := (Rat.cast_le (K:=ℝ)).mpr mag
  have xe := (Rat.cast_le (K:=ℝ)).mpr x
  have ye := (Rat.cast_le (K:=ℝ)).mpr y
  push_cast at m xe ye
  change |z 3*Real.cos (z 5)-z 2*Real.sin (z 5)-(r.x:ℝ)|≤_ ∧
         |z 3*Real.sin (z 5)+z 2*Real.cos (z 5)-(r.y:ℝ)|≤_
  constructor
  · apply abs_le.mpr
    obtain ⟨a,b⟩:=abs_le.mp A
    obtain ⟨c₁,d⟩:=abs_le.mp B
    obtain ⟨x₁,x₂⟩:=abs_le.mp xe
    dsimp only [r,z]; constructor <;> linarith
  · apply abs_le.mpr
    obtain ⟨a,b⟩:=abs_le.mp C
    obtain ⟨c₁,d⟩:=abs_le.mp D
    obtain ⟨y₁,y₂⟩:=abs_le.mp ye
    dsimp only [r,z]; constructor <;> linarith

end
end SolitonClassification.Rotating.IntegerTarget.CrossingCharts
#print axioms SolitonClassification.Rotating.IntegerTarget.CrossingCharts.position_errors

