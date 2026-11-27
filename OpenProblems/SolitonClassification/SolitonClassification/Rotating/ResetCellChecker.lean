import SolitonClassification.Rotating.ResetExpression
import SolitonClassification.Rotating.WindingMiddleReset

namespace SolitonClassification.Rotating.DyadicReset.CellCheck
open Middle

def sufficient (e : Term) : Bool := Id.run do
  let biased := e.packed (2*halfBase)+laneOffset*repunit
  return decide (e.degree<157 ∧ (e.mass:ℤ)<halfBase ∧ 0≤biased ∧ (biased.toNat &&& mask)=biased.toNat)

/-- Treats all coefficient cancellations and the decoded residual as the
actual value of the polynomial, for every time in the unit cell. -/
theorem real_bound (e : Term) (h : sufficient e=true) {t : ℝ} (ht : |t|≤1) :
    |e.realValue t|≤(commonDen:ℝ)/10^64 := by
  let v := e.packed (2*halfBase)
  let b := v+laneOffset*repunit
  have cs : e.degree<157 ∧ (e.mass:ℤ)<halfBase ∧ 0≤b ∧ b.toNat &&& mask=b.toNat := of_decide_eq_true h
  have high : b.toNat<((2:ℕ)^1280)^157 := (cs.2.2.2.symm.le.trans Nat.and_le_right).trans_lt mask_capacity.2
  have offset : (laneOffset.toNat:ℤ)=laneOffset := by decide +kernel
  have eq : v=(b.toNat:ℤ)-laneOffset.toNat*pack (2*halfBase) (List.replicate 157 1) := by
    rw [Int.toNat_of_nonneg cs.2.2.1,offset,←rep_correct]
    dsimp only [b]; ring
  have bd := mask_l1 (w:=1280) (k:=halfBase) (L:=laneOffset.toNat) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) high eq cs.2.2.2
    (fun a ha=>of_decide_eq_true (List.all_eq_true.mp mask_capacity.1 a ha))
  have bdi : ((l1 (extract halfBase 157 v)):ℤ)≤157*laneOffset := by
    rw [←offset]; exact_mod_cast bd
  have num := (mul_le_mul_of_nonneg_right bdi (by norm_num : (0:ℤ)≤10^64)).trans scalar_budget
  have realNum : ((l1 (extract halfBase 157 v)):ℝ)*10^64≤(commonDen:ℝ) := by exact_mod_cast num
  exact (e.bound (by decide +kernel : 0<halfBase) cs.1 cs.2.1 ht).trans
    ((le_div_iff₀ (by norm_num : (0:ℝ)<10^64)).mpr realNum)

end SolitonClassification.Rotating.DyadicReset.CellCheck
#print axioms SolitonClassification.Rotating.DyadicReset.CellCheck.real_bound
