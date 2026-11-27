import SolitonClassification.Rotating.IntegerGlobalNodeArithmetic
import SolitonClassification.Rotating.ResetHullSamples
import SolitonClassification.Rotating.ResetCompletePlus
import SolitonClassification.Rotating.ResetCompleteMinus

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
noncomputable section
open Set DyadicReset
set_option maxHeartbeats 2400000

def referenceState (c : Parameters) (j : ℤ) :=
  wideFlow ((j:ℝ)*step Middle.hn,shootingInitial phase c)

private theorem actual_signed_node (c : Parameters) (hc : c∈cube) (j : ℤ) (hj : j.natAbs<4000) (k : Fin 6) :
    |referenceState c j k-(qG (lane (positionNode j) k.val):ℝ)|≤5/10^26 := by
  have eq (n : Node) : rationalState n k=qG (lane n k.val) := by
    simp [rationalState,lane,qG,G,nodeGrid]
  cases j with
  | ofNat i =>
    have h := prefix_node_coordinates CompletePlus.tape (by decide) (by decide) (signedHalfSteps true)
      ((CompletePlus.range 0 (by decide)).1.trans rfl) hc i hj k
    have n : CompletePlus.tape.node i=GridPlus.atNode i := (CompletePlus.range _ hj).1
    rw [n,eq] at h
    exact h
  | negSucc i =>
    have h := prefix_node_coordinates CompleteMinus.tape (by decide) (by decide) (signedHalfSteps false)
      ((CompleteMinus.range 0 (by decide)).1.trans rfl) hc (i+1) hj k
    have n : CompleteMinus.tape.node (i+1)=GridMinus.atNode (i+1) := (CompleteMinus.range _ hj).1
    rw [n,eq] at h
    have tm : ((Int.negSucc i:ℤ):ℝ)*step Middle.hn=((i+1:ℕ):ℝ)*step (-Middle.hn) := by
      simp [step]; ring
    unfold referenceState
    rw [tm]
    exact h

private theorem product_error {z v p b : ℝ} (zz : |z-p|≤5/10^26)
    (unit : |v|≤1) (vb : |v-b|≤2/10^6) :
    |z*v-p*b|≤5/10^26+|p| *(2/10^6) := by
  rw [show z*v-p*b=(z-p)*v+p*(v-b) by ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul]
  have A := mul_le_mul zz unit (abs_nonneg _) (by norm_num : (0:ℝ)≤5/10^26)
  have B := mul_le_mul_of_nonneg_left vb (abs_nonneg p)
  linarith

theorem position_of_checked (c : Parameters) (hc : c∈cube) (r : RefPoint) (a : NodeAngles)
    (good : nodeChecked r a) :
    let v := segmentPosition c ((r.index:ℝ)*step Middle.hn)
    |v.1-(r.x:ℝ)/10^6|≤1/10000 ∧ |v.2-(r.y:ℝ)/10^6|≤1/10000 := by
  obtain ⟨idx,phaseBound,mag,start,un,st,coords⟩ := good
  let n := positionNode r.index
  let z := referenceState c r.index
  let p := qG (lane n 2)
  let q := qG (lane n 3)
  let th := qG (lane n 5)
  let C := qD (a.C 16)
  let S := qD (a.S 16)
  have pe : |z 2-(p:ℝ)|≤5/10^26 := actual_signed_node c hc r.index idx 2
  have qe : |z 3-(q:ℝ)|≤5/10^26 := actual_signed_node c hc r.index idx 3
  have te : |z 5-(th:ℝ)|≤5/10^26 := actual_signed_node c hc r.index idx 5
  have d := fine_angles_sound (rational_phases _ a phaseBound start un st)
  change |Real.cos (th:ℝ)-(C:ℝ)|≤1/10^6 ∧ |Real.sin (th:ℝ)-(S:ℝ)|≤1/10^6 at d
  have cc : |Real.cos (z 5)-(C:ℝ)|≤2/10^6 := by
    have y := (Real.abs_cos_sub_cos_le _ _).trans te
    exact (abs_sub_le _ (Real.cos (th:ℝ)) _).trans (by linarith only [y,d.1])
  have ss : |Real.sin (z 5)-(S:ℝ)|≤2/10^6 := by
    have y := (Real.abs_sin_sub_sin_le _ _).trans te
    exact (abs_sub_le _ (Real.sin (th:ℝ)) _).trans (by linarith only [y,d.2])
  have A := product_error qe (Real.abs_cos_le_one _) cc
  have B := product_error pe (Real.abs_sin_le_one _) ss
  have F := product_error qe (Real.abs_sin_le_one _) ss
  have J := product_error pe (Real.abs_cos_le_one _) cc
  obtain ⟨m,x,y⟩ := rational_coordinates _ _ a r mag coords
  change |p|+|q|≤15 at m
  change |q*C-p*S-(r.x:ℚ)/10^6|≤1/10^6 at x
  change |q*S+p*C-(r.y:ℚ)/10^6|≤1/10^6 at y
  have m' := (Rat.cast_le (K:=ℝ)).mpr m
  have x' := (Rat.cast_le (K:=ℝ)).mpr x
  have y' := (Rat.cast_le (K:=ℝ)).mpr y
  push_cast at m' x' y'
  change |z 3*Real.cos (z 5)-z 2*Real.sin (z 5)-(r.x:ℝ)/10^6|≤_ ∧
    |z 3*Real.sin (z 5)+z 2*Real.cos (z 5)-(r.y:ℝ)/10^6|≤_
  constructor
  · obtain ⟨a₁,a₂⟩ := abs_le.mp A
    obtain ⟨b₁,b₂⟩ := abs_le.mp B
    obtain ⟨x₁,x₂⟩ := abs_le.mp x'
    apply abs_le.mpr; constructor <;> linarith only [a₁,a₂,b₁,b₂,x₁,x₂,m']
  · obtain ⟨a₁,a₂⟩ := abs_le.mp F
    obtain ⟨b₁,b₂⟩ := abs_le.mp J
    obtain ⟨y₁,y₂⟩ := abs_le.mp y'
    apply abs_le.mpr; constructor <;> linarith only [a₁,a₂,b₁,b₂,y₁,y₂,m']

end
end SolitonClassification.Rotating.IntegerTarget.GlobalCount
#print axioms SolitonClassification.Rotating.IntegerTarget.GlobalCount.position_of_checked
