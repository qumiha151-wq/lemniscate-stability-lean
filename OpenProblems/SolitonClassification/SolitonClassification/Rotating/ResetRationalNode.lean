import SolitonClassification.Rotating.ResetPolynomialMetric
import SolitonClassification.Rotating.PointMatrixCertificate

namespace SolitonClassification.Rotating.DyadicReset
open Finset
def invGrid : ℕ := 10^12
def nodeGrid : ℕ := 2^240
def commonGrid : ℕ := nodeGrid*invGrid
abbrev Node := Array ℤ
def nodeLane (node : Node) (j i : Fin 6) : ℤ :=
  if j.val=5 then (if i.val=5 then nodeGrid else 0)
  else if i.val=4 then (if j.val=4 then nodeGrid else 0)
  else (node[6+5*j.val+(if i.val=5 then 4 else i.val)]?).getD 0
def forwardNode (node : Node) : PointMatrix := fun j i=>nodeLane node j i * invGrid
def inverseNode (inverse : Node) : PointMatrix :=
  fun j i=>(inverse[6*j.val+i.val]?).getD 0 * nodeGrid

def CheckedNode (n w : Node) : Prop :=
  (∀i,∑j : Fin 6,|(forwardNode n) j i|≤2900*(commonGrid:ℤ)) ∧
  (∀i,∑j : Fin 6,|(inverseNode w) j i|≤3490*(commonGrid:ℤ)) ∧
  (∀i,∑j : Fin 6,|pointMatrixDefect commonGrid (forwardNode n) (inverseNode w) j i|≤(commonGrid:ℤ)^2/1000) ∧
  (∀i,∑j : Fin 6,|pointMatrixDefect commonGrid (inverseNode w) (forwardNode n) j i|≤(commonGrid:ℤ)^2/1000)
instance (n w : Node) : Decidable (CheckedNode n w) := by unfold CheckedNode;infer_instance

noncomputable section
theorem checkedNodeBounds {n w : Node} (C : CheckedNode n w) :
    IsUnit (pointMatrixOperator commonGrid (forwardNode n)) ∧
    ‖pointMatrixOperator commonGrid (forwardNode n)‖≤2900 ∧
    ‖Ring.inverse (pointMatrixOperator commonGrid (forwardNode n))‖≤3500 := by
  obtain ⟨nF,nW,right,left⟩ := C
  have hf := pointMatrixOperator_norm (S:=commonGrid) (by decide +kernel) (forwardNode n)
      (by decide +kernel : 0≤2900*(commonGrid:ℤ)) nF
  obtain ⟨hu,hi⟩ := pointMatrix_inverse_certificate (S:=commonGrid) (by decide +kernel)
    (forwardNode n) (inverseNode w) (by decide +kernel : 0≤3490*(commonGrid:ℤ))
    (by decide +kernel : 0≤(commonGrid:ℤ)^2/1000) nW left right (by norm_num [commonGrid,nodeGrid,invGrid])
  refine ⟨hu,hf.trans ?_,hi.trans ?_⟩ <;> norm_num [commonGrid,nodeGrid,invGrid]

theorem matrixPath_zero_eq {p : Data} {n : Node}
    (h : ∀i : ℕ,(p i).head?.getD 0=(n[i]?).getD 0) :
    matrixPath p 0=pointMatrixOperator commonGrid (forwardNode n) := by
  unfold matrixPath pointMatrixOperator rationalColumnOperator
  apply congrArg columnOperator; funext j i
  change fullColumn p j 0 i=(((forwardNode n j i:ℚ)/commonGrid:ℚ):ℝ)
  rw [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]
  unfold fullColumn forwardNode nodeLane column columnOf
  simp only [eval_zero,h]
  by_cases j5 : j.val<5
  · have je : j.val≠5 := by omega
    simp only [dif_pos j5,if_neg je]
    by_cases i4 : i.val=4
    · simp only [if_pos i4];split <;> norm_num [d,Middle.den,commonGrid,nodeGrid,invGrid]
    · simp only [if_neg i4,Int.cast_mul,Int.cast_natCast]
      norm_num [d,Middle.den,commonGrid,nodeGrid,invGrid];ring
  · have je : j.val=5 := by omega
    simp only [dif_neg j5,if_pos je,coordinateBasis]
    by_cases i5 : i=(5:Fin 6)
    · subst i; norm_num [commonGrid,nodeGrid,invGrid]
    · have ie : i.val≠5 := by intro e;apply i5; exact Fin.ext e
      simp [i5,ie]
end
end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.checkedNodeBounds
