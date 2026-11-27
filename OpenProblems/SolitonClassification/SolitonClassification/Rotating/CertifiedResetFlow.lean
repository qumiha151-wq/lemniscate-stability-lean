import SolitonClassification.Rotating.ResetCellMath
import SolitonClassification.Rotating.ResetCellChecker

noncomputable section
open Set
namespace SolitonClassification.Rotating.DyadicReset
open CellCheck
def h : ℝ := (Middle.hn:ℝ)/Middle.hd
def eps : ℝ := 1/10^64

structure Certified (p : Data) : Prop where
  ok : ∀i : Fin 31, sufficient (defectTerm p Middle.den Middle.hn Middle.hd i)=true

private theorem divide_bound {a v : ℝ} (pos : 0<(Middle.commonDen:ℝ))
    (ha : a=(Middle.commonDen:ℝ)*v) (bd : |a|≤(Middle.commonDen:ℝ)/10^64) : |v|≤eps := by
  rw [ha,abs_mul,abs_of_pos pos] at bd
  apply le_of_mul_le_mul_left (a:=(Middle.commonDen:ℝ)) _ pos
  simpa only [eps,div_eq_mul_inv,one_mul] using bd

theorem certified_state {p : Data} (C : Certified p) {t : ℝ} (ht : t∈Icc 0 1) :
    ‖velocity p Middle.den t-h • Rotating.field (path p Middle.den t)‖≤eps := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num [eps])).mpr
  intro i
  rw [Real.norm_eq_abs]
  let ix : Fin 31 := ⟨i.val,by omega⟩
  apply divide_bound (a:=(defectTerm p Middle.den Middle.hn Middle.hd i).realValue t)
    (by exact_mod_cast (by decide +kernel : 0<Middle.commonDen))
  · change _=(Middle.commonDen:ℝ)*(velocity p Middle.den t i-h*Rotating.field (path p Middle.den t) i)
    rw [state_identity p (by norm_num [Middle.den]) (by norm_num [Middle.hd])]
    unfold Middle.commonDen h
    push_cast; ring
  · exact real_bound _ (C.ok ix) (by rw [abs_of_nonneg ht.1]; exact ht.2)

theorem certified_variation {p : Data} (C : Certified p) {t : ℝ} (ht : t∈Icc 0 1) (j : Fin 5) :
    ‖columnVelocity p Middle.den j t-h • linear (path p Middle.den t) (column p Middle.den j t)‖≤eps := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num [eps])).mpr
  intro i
  rw [Real.norm_eq_abs]
  by_cases hz : i.val=4
  · have hi : i=(4:Fin 6) := Fin.ext hz
    subst i
    change |(0:ℝ)-h*0|≤eps
    norm_num [eps]
  · have sz : slot i j<31 := by unfold slot; split <;> omega
    let ix : Fin 31 := ⟨slot i j,sz⟩
    apply divide_bound (a:=(defectTerm p Middle.den Middle.hn Middle.hd (slot i j)).realValue t)
      (by exact_mod_cast (by decide +kernel : 0<Middle.commonDen))
    · change _=(Middle.commonDen:ℝ)*(columnVelocity p Middle.den j t i-h*(linear _ _) i)
      rw [column_identity p (by norm_num [Middle.den]) (by norm_num [Middle.hd]) t j i hz]
      unfold Middle.commonDen h
      push_cast; ring
    · exact real_bound _ (C.ok ix) (by rw [abs_of_nonneg ht.1];exact ht.2)

theorem eval_zero (p : List ℤ) : eval 0 p=(p.head?.getD 0:ℤ) := by cases p <;> simp [eval]
theorem eval_one (p : List ℤ) : eval 1 p=(p.sum:ℝ) := by
  induction p with | nil => simp [eval] | cons a p ih => simp [eval,ih]

/-- Coordinatewise node equality implies exact matching of all six state
coordinates and all five variational columns, including the constant row. -/
theorem adjacent_matching {p q : Data} (matchNodes : ∀i,(p i).sum=((q i).head?.getD 0)) :
    path p Middle.den 1=path q Middle.den 0 ∧
      ∀j,column p Middle.den j 1=column q Middle.den j 0 := by
  have same (i : ℕ) : eval 1 (p i)=eval 0 (q i) := by
    rw [eval_one,eval_zero,matchNodes]
  constructor
  · funext i; simp only [path,same]
  · intro j; funext i; simp only [column,columnOf,same]

end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.certified_variation
