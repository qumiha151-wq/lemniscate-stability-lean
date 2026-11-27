import SolitonClassification.Rotating.IntegerWideFlow

namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
open Set Metric Filter DyadicReset
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- At every point of a complete signed tape the previously constructed
variational solution is the derivative of one specified two-sided flow. -/
theorem fixed_time_shooting_bounds {n : ℤ} (T : PolynomialTape n 4000)
    (hs : |step n|≤1/125) (origin : matrixPath (T.data 0) 0=1) :
    ∀a∈ball (path (T.data 0) d 0) (2/10^30), ∀i : ℕ,i<4000→∀t∈unitCell,
    let time := ((i:ℝ)+t)*step n
    let y := wideFlow (time,a)
    let S := fun b : State => wideFlow (time,b)
    StateBox y ∧ HasDerivAt (fun v => wideFlow (v,a)) (field y) time ∧
    ‖y-path (T.data i) d t‖≤5/10^26 ∧
    (‖a-path (T.data 0) d 0‖≤1/10^71 → ‖y-path (T.data i) d t‖≤5/10^52) ∧
    HasFDerivAt S (fderiv ℝ S a) a ∧
    ‖fderiv ℝ S a-matrixPath (T.data i) t‖≤3/10^12 := by
  obtain ⟨X,hX⟩ := shooting_family T hs origin
  let B := ball (path (T.data 0) d 0) (2/10^30)
  have box (a : State) (ha : a∈B) (i : ℕ) (hi : i<4000) (t : ℝ) (ht : t∈unitCell) :
      StateBox (X a i t) := by
    intro j hj
    have p := (lift_inner (T.small i hi) ht).1 j hj
    change |path (T.data i) d t j|≤9 at p
    have err := (coordinate_bound (X a i t-path (T.data i) d t) j).trans
      (((hX a ha).2.2 i hi t ht).1)
    change |X a i t j-path (T.data i) d t j|≤_ at err
    have tri := abs_add_le (X a i t j-path (T.data i) d t j) (path (T.data i) d t j)
    rw [sub_add_cancel] at tri
    linarith only [p,err,tri]
  have same (a : State) (ha : a∈B) := joined_identification
    (hs.trans (by norm_num)) (hX a ha).1 (hX a ha).2.1 (box a ha)
  intro a ha i hi t ht
  let time := ((i:ℝ)+t)*step n
  let S := fun b : State => wideFlow (time,b)
  let U := fun b : State => X b i t
  have eqv : X a i t=wideFlow (time,a) := same a ha i hi t ht
  have boxy : StateBox (wideFlow (time,a)) := eqv ▸ box a ha i hi t ht
  have eq : S=ᶠ[𝓝 a] U := by
    filter_upwards [isOpen_ball.mem_nhds ha] with b hb
    exact (same b hb i hi t ht).symm
  have bounds := (hX a ha).2.2 i hi t ht
  have df : HasFDerivAt S (fderiv ℝ U a) a := bounds.2.2.1.congr_of_eventuallyEq eq
  change StateBox (wideFlow (time,a)) ∧ _
  refine ⟨boxy,?_,eqv ▸ bounds.1,?_,?_,?_⟩
  · simpa only [wideField,wideClip_id boxy] using wideFlow_time a time
  · intro h
    exact eqv ▸ bounds.2.1 h
  · exact df.differentiableAt.hasFDerivAt
  · change ‖fderiv ℝ S a-matrixPath (T.data i) t‖≤_
    rw [df.fderiv]
    exact bounds.2.2.2

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.fixed_time_shooting_bounds
