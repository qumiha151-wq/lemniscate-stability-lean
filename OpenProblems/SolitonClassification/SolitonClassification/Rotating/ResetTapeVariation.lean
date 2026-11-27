import SolitonClassification.Rotating.ResetMetricVariation
namespace SolitonClassification.Rotating.DyadicReset
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

theorem matrixSlope_cont (p : Data) : Continuous (matrixSlope p) := by
  unfold matrixSlope columnOperator
  apply continuous_finsetSum
  intro j hj
  let L := ContinuousLinearMap.smulRightL ℝ State State (ContinuousLinearMap.proj j)
  change Continuous (fun s=>L (fullSlope p j s))
  apply L.continuous.comp
  unfold fullSlope
  split
  · apply continuous_pi
    intro i
    unfold columnVelocity
    split
    · exact continuous_const
    · exact (eval_cont _).div_const _
  · exact continuous_const

theorem tape_variation {n : ℤ} {N : ℕ} (T : PolynomialTape n N) (positive : 0<N)
    (hs : |step n|≤1/125) (x : ℕ→ℝ→State) {D : ℝ} (hD : D≤1)
    (der : ∀i,i<N→FollowsState (step n) (x i))
    (close : ∀i,i<N→∀t∈unitCell,‖x i t-path (T.data i) d t‖≤D)
    (h8 : coefficientBound D≤1/8) (h4 : (N:ℝ)*(2*coefficientBound D)≤1/4) :
    ∃J : ℕ→ℝ→FlowEnd, ∀i,i<N →
      J i 0=(if i=0 then matrixPath (T.data 0) 0 else J (i-1) 1) ∧
      (∀t∈unitCell,HasDerivWithinAt (J i) (actualCoefficient (step n) (x i) t*J i t) unitCell t) ∧
      ∀t∈unitCell,‖J i t-matrixPath (T.data i) t‖≤5000*((i:ℝ)+1)*(2*coefficientBound D) := by
  classical
  let p (i : ℕ) (hi : i<N) : MetricCell (step n) :=
    let hnode := matrixPath_zero_eq (p:=T.data i) (T.initial i hi)
    let inv := checkedNodeBounds (T.inverse_ok i hi)
    polynomialMetric (T.residual i hi) (T.small i hi) hs
      (hnode.symm ▸ inv.1) (hnode.symm ▸ inv.2.1) (hnode.symm ▸ inv.2.2)
  let c (i : ℕ) := if g : i<N then p i g else p 0 positive
  have eq (i : ℕ) (hi : i<N) : c i=p i hi := dif_pos hi
  have ck (i : ℕ) (hi : i<N) : (c i).Q=path (T.data i) d := by rw [eq i hi];rfl
  have cm (i : ℕ) (hi : i<N) : (c i).M=matrixPath (T.data i) := by rw [eq i hi];rfl
  have cd (i : ℕ) (hi : i<N) : ContinuousOn (c i).dM unitCell := by rw [eq i hi]; exact (matrixSlope_cont _).continuousOn
  have cj (i : ℕ) (hi : i+1<N) : (c i).M 1=(c (i+1)).M 0 := by
    simp only [cm i (by omega),cm (i+1) hi]; exact (matrixPath_join (T.matched i hi)).2
  obtain ⟨J,hJ⟩ := variation_chain c N x (hs.trans (by norm_num)) hD der
    (fun i hi=>by rw [ck i hi];exact close i hi) cd cj h8 h4
  refine ⟨J,fun i hi=>?_⟩
  simpa only [cm i hi,cm 0 positive] using hJ i hi

theorem variation_budget_centre :
    coefficientBound (5/(10:ℝ)^52)≤1/8 ∧ 4000*(2*coefficientBound (5/(10:ℝ)^52))≤1/4 ∧
    5000*4000*(2*coefficientBound (5/(10:ℝ)^52))≤3/(10:ℝ)^38 := by
  norm_num [coefficientBound,eps]
theorem variation_budget_cube :
    coefficientBound (5/(10:ℝ)^26)≤1/8 ∧ 4000*(2*coefficientBound (5/(10:ℝ)^26))≤1/4 ∧
    5000*4000*(2*coefficientBound (5/(10:ℝ)^26))≤3/(10:ℝ)^12 := by
  norm_num [coefficientBound,eps]
end
end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.tape_variation
