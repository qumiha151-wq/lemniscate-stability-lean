import SolitonClassification.Rotating.ResetRationalNode
namespace SolitonClassification.Rotating.DyadicReset
open Finset
def sum6 (f : Fin 6→ℤ) := f 0+f 1+f 2+f 3+f 4+f 5
theorem sum6_eq (f : Fin 6→ℤ) : sum6 f=∑j,f j := by
  simp [sum6,Fin.sum_univ_succ];ring
def six (f : Fin 6→Bool) := f 0 && f 1 && f 2 && f 3 && f 4 && f 5
theorem six_spec (f : Fin 6→Bool) (h : six f=true) (j : Fin 6) : f j=true := by
  simp only [six,Bool.and_eq_true] at h
  fin_cases j <;> tauto
def witLane (w : Node) (j i : Fin 6) := (w[6*j.val+i.val]?).getD 0
def directProduct (X Y : PointMatrix) (j i : Fin 6) := sum6 fun k=>X k i*Y j k
def directError (X Y : PointMatrix) (j i : Fin 6) :=
  directProduct X Y j i-(if i=j then (commonGrid:ℤ) else 0)
def fastNode (n w : Node) : Bool := six fun i =>
  decide (sum6 (fun j=>|(nodeLane n) j i|)≤2900*(nodeGrid:ℤ)) &&
  decide (sum6 (fun j=>|(witLane w) j i|)≤3490*(invGrid:ℤ)) &&
  decide (1000*sum6 (fun j=>|directError (nodeLane n) (witLane w) j i|)≤(commonGrid:ℤ)) &&
  decide (1000*sum6 (fun j=>|directError (witLane w) (nodeLane n) j i|)≤(commonGrid:ℤ))

theorem fastNode_sound {n w : Node} (h : fastNode n w=true) : CheckedNode n w := by
  have single (i : Fin 6) := six_spec _ h i
  simp only [Bool.and_eq_true,decide_eq_true_eq] at single
  have grid : (commonGrid:ℤ)=(nodeGrid:ℤ)*(invGrid:ℤ) := by simp [commonGrid]
  have scale (k : ℤ) (hk : 0≤k) (f : Fin 6→ℤ) :
      (∑j,|f j*k|)=sum6 (fun j=>|f j|)*k := by
    simp only [abs_mul,abs_of_nonneg hk,sum6_eq,Finset.sum_mul]
  have err (A B : PointMatrix) (u v : ℤ) (huv : u*v=(commonGrid:ℤ)) (j i : Fin 6) :
      pointMatrixDefect commonGrid (fun j i=>A j i*u) (fun j i=>B j i*v) j i=
      directError A B j i*(commonGrid:ℤ) := by
    simp only [pointMatrixDefect,pointMatrixProduct,directError,directProduct,sum6_eq,sub_mul,Finset.sum_mul]
    have pq (k : Fin 6) : (A k i*u)*(B j k*v)=A k i*B j k*commonGrid := by rw [←huv];ring
    simp only [pq]
    split <;> ring
  have res (A B : PointMatrix) (u v : ℤ) (huv : u*v=(commonGrid:ℤ)) (i : Fin 6)
      (bound : 1000*sum6 (fun j=>|directError A B j i|)≤(commonGrid:ℤ)) :
      (∑j,|pointMatrixDefect commonGrid (fun j i=>A j i*u) (fun j i=>B j i*v) j i|)≤(commonGrid:ℤ)^2/1000 := by
    simp only [err A B u v huv]
    rw [scale _ (by positivity)]
    apply (Int.le_ediv_iff_mul_le (by decide : (0:ℤ)<1000)).mpr
    have m := mul_le_mul_of_nonneg_right bound (show (0:ℤ)≤commonGrid by positivity)
    nlinarith only [m]
  constructor
  · intro i
    change (∑j,|(nodeLane n j i)*(invGrid:ℤ)|)≤_
    rw [scale _ (by positivity),grid,←mul_assoc]
    exact mul_le_mul_of_nonneg_right (single i).1.1.1 (by positivity)
  constructor
  · intro i
    change (∑j,|(witLane w j i)*(nodeGrid:ℤ)|)≤_
    rw [scale _ (by positivity),grid,mul_comm (nodeGrid:ℤ) invGrid,←mul_assoc]
    exact mul_le_mul_of_nonneg_right (single i).1.1.2 (by positivity)
  constructor
  · intro i
    exact res (nodeLane n) (witLane w) _ _ (by simpa [mul_comm] using grid.symm) i (single i).1.2
  · intro i
    exact res (witLane w) (nodeLane n) _ _ grid.symm i (single i).2
end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.fastNode_sound
