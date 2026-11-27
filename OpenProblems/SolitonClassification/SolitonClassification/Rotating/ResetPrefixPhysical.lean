import SolitonClassification.Rotating.IntegerTerminalRows

namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
open Set Metric DyadicReset
set_option maxHeartbeats 1500000

/-- A verified prefix controls one and the same physical shooting trajectory
for every initial parameter in the closing cube. -/
theorem prefix_physical {n : ℤ} {N : ℕ} (T : PolynomialTape n N)
    (hN : 0<N) (cap : N≤4000) (hs : |step n|≤1/125)
    (first : T.node 0=initialNode) {c : Parameters} (hc : c∈cube) :
    ∀i : ℕ,i<N→∀t∈unitCell,
      let time := ((i:ℝ)+t)*step n
      let z := wideFlow (time,shootingInitial phase c)
      HasDerivAt (fun v => wideFlow (v,shootingInitial phase c)) (field z) time ∧
      ‖z-path (T.data i) d t‖≤5/10^26 := by
  have init (j : ℕ) : ((T.data 0 j).head?.getD 0)=(initialNode[j]?).getD 0 := by
    rw [T.initial 0 hN,first]
  have initP (j : ℕ) := PrefixPlus.tape.initial 0 (by decide) j
  have orig : path (T.data 0) d 0=path (PrefixPlus.tape.data 0) d 0 := by
    ext i
    change eval 0 _ / (d:ℝ)=eval 0 _ / (d:ℝ)
    rw [eval_zero,eval_zero,init,initP]
    rfl
  have M0 : matrixPath (T.data 0) 0=1 :=
    (matrixPath_zero_eq init).trans ((matrixPath_zero_eq initP).symm.trans PrefixPlus.at_zero)
  have near : ‖shootingInitial phase center-path (T.data 0) d 0‖≤1/10^71 := by
    rw [initial_coordinate,orig]
    exact PrefixPlus.centre_seed
  let a := shootingInitial phase c
  have change := shootingInitial_norm_bound phase (by norm_num [phase,phaseQ]) (by norm_num [phase,phaseQ]) (c-center)
  rw [map_sub] at change
  have dist : ‖a-path (T.data 0) d 0‖≤2/10^30 :=
    (norm_sub_le_norm_sub_add_norm_sub _ (shootingInitial phase center) _).trans (by
      have r : ‖c-center‖≤1/(10:ℝ)^30 := hc
      dsimp [a]; linarith)
  have start : ‖Ring.inverse (matrixPath (T.data 0) 0) (a-path (T.data 0) d 0)‖≤2/10^30 := by
    rwa [M0,Ring.inverse_one]
  have cap' : (N:ℝ)≤4000 := by exact_mod_cast cap
  have inc : 0 ≤ increment (1/(10:ℝ)^29) := by norm_num [increment,roughPhysical,eps]
  have budget := mul_le_mul_of_nonneg_right cap' inc
  obtain ⟨x,hx⟩ := tape_transport T hN hs a (by norm_num : (0:ℝ)≤1/10^29)
    cube_4000_budget.1 cube_4000_budget.2.1 start (by linarith [cube_4000_budget.2.2])
  have err (i : ℕ) (hi : i<N) (t : ℝ) (ht : t∈unitCell) :
      ‖x i t-path (T.data i) d t‖≤5/10^26 := ((hx i hi).2.2 t ht).trans_eq (by norm_num)
  have box (i : ℕ) (hi : i<N) (t : ℝ) (ht : t∈unitCell) : StateBox (x i t) := by
    intro j hj
    have ref := (lift_inner (T.small i hi) ht).1 j hj
    change |path (T.data i) d t j|≤9 at ref
    have dif := (coordinate_bound (x i t-path (T.data i) d t) j).trans (err i hi t ht)
    change |x i t j-path (T.data i) d t j|≤_ at dif
    have tri := abs_add_le (x i t j-path (T.data i) d t j) (path (T.data i) d t j)
    rw [sub_add_cancel] at tri
    change |x i t j|≤10
    linarith only [ref,dif,tri]
  have same := joined_identification (hs.trans (by norm_num)) (fun i hi => (hx i hi).1)
    (fun i hi => (hx i hi).2.1) box
  intro i hi t ht
  have ident := same i hi t ht
  have bx := ident ▸ box i hi t ht
  refine ⟨?_,ident ▸ err i hi t ht⟩
  simpa only [wideField,wideClip_id bx] using wideFlow_time a (((i:ℝ)+t)*step n)

theorem prefix_node_coordinates {n : ℤ} {N : ℕ} (T : PolynomialTape n N)
    (hN : 0<N) (cap : N≤4000) (hs : |step n|≤1/125)
    (first : T.node 0=initialNode) {c : Parameters} (hc : c∈cube) (i : ℕ) (hi : i<N)
    (j : Fin 6) :
    |wideFlow ((i:ℝ)*step n,shootingInitial phase c) j-(rationalState (T.node i) j:ℝ)|≤5/10^26 := by
  have h := (prefix_physical T hN cap hs first hc i hi 0 (by norm_num [unitCell])).2
  simp only [add_zero] at h
  have eq : path (T.data i) d 0 j=(rationalState (T.node i) j:ℝ) := by
    change eval 0 _ / (d:ℝ)=_
    rw [eval_zero,T.initial i hi j]
    simp [rationalState,d,Middle.den,nodeGrid]
  have e := (coordinate_bound (wideFlow ((i:ℝ)*step n,shootingInitial phase c)-path (T.data i) d 0) j).trans h
  simpa only [Pi.sub_apply,eq] using e

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.prefix_node_coordinates
