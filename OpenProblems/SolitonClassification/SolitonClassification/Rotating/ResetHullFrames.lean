import SolitonClassification.Rotating.ResetPrefixPhysical
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
open Set DyadicReset
set_option maxHeartbeats 1600000

def framePosition (z : State) : ℝ × ℝ :=
  (z 3*Real.cos (z 5)-z 2*Real.sin (z 5),z 3*Real.sin (z 5)+z 2*Real.cos (z 5))

/-- Change of angle in a Frenet frame, applied in physical position units. -/
theorem frame_bound (z : State) {θ σ : ℝ} (cs : Real.cos θ=σ) (sn : Real.sin θ=0)
    (ang : |z 5-θ|≤1/250) (bound : |z 2|+|z 3|≤5) :
    |(framePosition z).1-z 3*σ|≤1/50 ∧ |(framePosition z).2-z 2*σ|≤1/50 := by
  have c := (Real.abs_cos_sub_cos_le (z 5) θ).trans ang
  have s := (Real.abs_sin_sub_sin_le (z 5) θ).trans ang
  rw [cs] at c
  rw [sn,sub_zero] at s
  have multi (x y : ℝ) (h : |y|≤1/250) : |x*y|≤|x| * (1/250) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg x)
  constructor
  · change |z 3*Real.cos (z 5)-z 2*Real.sin (z 5)-z 3*σ|≤1/50
    rw [show z 3*Real.cos (z 5)-z 2*Real.sin (z 5)-z 3*σ=z 3*(Real.cos (z 5)-σ)-z 2*Real.sin (z 5) by ring]
    exact (abs_sub _ _).trans (by linarith [multi (z 3) _ c,multi (z 2) _ s])
  · change |z 3*Real.sin (z 5)+z 2*Real.cos (z 5)-z 2*σ|≤1/50
    rw [show z 3*Real.sin (z 5)+z 2*Real.cos (z 5)-z 2*σ=z 3*Real.sin (z 5)+z 2*(Real.cos (z 5)-σ) by ring]
    exact (abs_add_le _ _).trans (by linarith [multi (z 3) _ s,multi (z 2) _ c])

theorem observed_coordinate {z : State} {node : Node} {j : Fin 6} {l u : ℚ}
    (e : |z j-(rationalState node j:ℝ)|≤5/10^26)
    (lo : l+1/10^20 ≤ rationalState node j)
    (hi : rationalState node j ≤ u-1/10^20) : (l:ℝ)≤z j ∧ z j≤(u:ℝ) := by
  have L := (Rat.cast_le (K:=ℝ)).mpr lo
  have H := (Rat.cast_le (K:=ℝ)).mpr hi
  push_cast at L H
  obtain ⟨a,b⟩ := abs_le.mp e
  constructor <;> linarith

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.frame_bound
