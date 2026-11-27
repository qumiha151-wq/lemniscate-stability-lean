import SolitonClassification.Rotating.ResetRationalNode
import SolitonClassification.Rotating.ResetMetricChain
namespace SolitonClassification.Rotating.DyadicReset
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

/-- All nontrivial per-cell hypotheses are finite statements over
dyadic integer coefficients and integer point-matrix witnesses. -/
structure PolynomialTape (n : ℤ) (N : ℕ) where
  data : ℕ→Data
  node : ℕ→Node
  inverse : ℕ→Node
  residual : ∀i,i<N → SignedCheck n (data i)
  small : ∀i,i<N → Small (data i)
  initial : ∀i,i<N → ∀j,((data i j).head?.getD 0)=((node i)[j]?).getD 0
  inverse_ok : ∀i,i<N → CheckedNode (node i) (inverse i)
  matched : ∀i,i+1<N → ∀j,(data i j).sum=(data (i+1) j).head?.getD 0

theorem tape_transport {n : ℤ} {N : ℕ} (T : PolynomialTape n N) (positive : 0<N)
    (smallStep : |step n|≤1/125) (a : State) {R r : ℝ} (R0 : 0≤R)
    (hr : 5000*R≤1/4) (hr1 : roughPhysical R≤1)
    (start : ‖Ring.inverse (matrixPath (T.data 0) 0) (a-path (T.data 0) d 0)‖≤r)
    (budget : r+(N:ℝ)*increment R≤R) :
    ∃x : ℕ→ℝ→State, ∀i,i<N →
      x i 0=(if i=0 then a else x (i-1) 1) ∧ FollowsState (step n) (x i) ∧
      ∀t∈unitCell,‖x i t-path (T.data i) d t‖≤5000*R := by
  classical
  let p (i : ℕ) (hi : i<N) : MetricCell (step n) :=
    let hnode := (matrixPath_zero_eq (p:=T.data i) (T.initial i hi))
    let inv := checkedNodeBounds (T.inverse_ok i hi)
    polynomialMetric (T.residual i hi) (T.small i hi) smallStep
      (hnode.symm ▸ inv.1) (hnode.symm ▸ inv.2.1) (hnode.symm ▸ inv.2.2)
  let c (i : ℕ) := if g : i<N then p i g else p 0 positive
  have cq (i : ℕ) (hi : i<N) : (c i).Q=path (T.data i) d := by
    simp only [c,dif_pos hi]; rfl
  have cm (i : ℕ) (hi : i<N) : (c i).M=matrixPath (T.data i) := by
    simp only [c,dif_pos hi]; rfl
  have join (i : ℕ) (hi : i+1<N) : (c i).Q 1=(c (i+1)).Q 0 ∧ (c i).M 1=(c (i+1)).M 0 := by
    simp only [cq i (by omega),cq (i+1) hi,cm i (by omega),cm (i+1) hi]
    exact matrixPath_join (T.matched i hi)
  have beginBound : ‖Ring.inverse ((c 0).M 0) (a-(c 0).Q 0)‖≤r := by
    simpa only [cm 0 positive,cq 0 positive] using start
  obtain ⟨x,hx⟩ := transport_chain c N a R0 (smallStep.trans (by norm_num)) hr hr1 join beginBound budget
  refine ⟨x,fun i hi=>⟨(hx i hi).1,(hx i hi).2.1,fun t ht=>?_⟩⟩
  have g := ((hx i hi).2.2 t ht).2
  simpa only [cq i hi] using g

theorem signedHalfSteps (sign : Bool) :
    |step (if sign then Middle.hn else -Middle.hn)|≤1/125 := by
  cases sign <;> norm_num [step,Middle.hn,Middle.hd]

theorem centre_tape {n : ℤ} (T : PolynomialTape n 4000) (smallStep : |step n|≤1/125)
    (a : State) (start : ‖Ring.inverse (matrixPath (T.data 0) 0) (a-path (T.data 0) d 0)‖≤1/10^71) :
    ∃x : ℕ→ℝ→State, ∀i,i<4000 →
      x i 0=(if i=0 then a else x (i-1) 1) ∧ FollowsState (step n) (x i) ∧
      ∀t∈unitCell,‖x i t-path (T.data i) d t‖≤5/10^52 := by
  obtain ⟨x,hx⟩ := tape_transport T (by decide) smallStep a (by norm_num : (0:ℝ)≤1/10^55)
    centre_4000_budget.1 centre_4000_budget.2.1 start (by simpa using centre_4000_budget.2.2)
  refine ⟨x,fun i hi=>⟨(hx i hi).1,(hx i hi).2.1,fun t ht=>((hx i hi).2.2 t ht).trans_eq ?_⟩⟩
  norm_num

theorem cube_tape {n : ℤ} (T : PolynomialTape n 4000) (smallStep : |step n|≤1/125)
    (a : State) (start : ‖Ring.inverse (matrixPath (T.data 0) 0) (a-path (T.data 0) d 0)‖≤2/10^30) :
    ∃x : ℕ→ℝ→State, ∀i,i<4000 →
      x i 0=(if i=0 then a else x (i-1) 1) ∧ FollowsState (step n) (x i) ∧
      ∀t∈unitCell,‖x i t-path (T.data i) d t‖≤5/10^26 := by
  obtain ⟨x,hx⟩ := tape_transport T (by decide) smallStep a (by norm_num : (0:ℝ)≤1/10^29)
    cube_4000_budget.1 cube_4000_budget.2.1 start (by simpa using cube_4000_budget.2.2)
  refine ⟨x,fun i hi=>⟨(hx i hi).1,(hx i hi).2.1,fun t ht=>((hx i hi).2.2 t ht).trans_eq ?_⟩⟩
  norm_num
end
end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.centre_tape
#print axioms SolitonClassification.Rotating.DyadicReset.cube_tape
