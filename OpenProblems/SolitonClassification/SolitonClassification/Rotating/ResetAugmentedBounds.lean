import SolitonClassification.Rotating.ResetCellMath

namespace SolitonClassification.Rotating.DyadicReset
noncomputable section
abbrev Aug := State × (Fin 5 → State)
def augmented (z : Aug) : Aug := (Rotating.field z.1, fun j => linear z.1 (z.2 j))

private structure Env (δ a b m l : ℝ) : Prop where
  left : |a|≤m
  right : |b|≤m
  change : |a-b|≤l*δ

private theorem constant (δ c : ℝ) : Env δ c c |c| 0 := ⟨le_rfl,le_rfl,by simp⟩
private theorem plusE {δ a b c d m l n k : ℝ} (h : Env δ a b m l) (g : Env δ c d n k) :
    Env δ (a+c) (b+d) (m+n) (l+k) := by
  refine ⟨(abs_add_le ..).trans (add_le_add h.left g.left),(abs_add_le ..).trans (add_le_add h.right g.right),?_⟩
  rw [show a+c-(b+d)=(a-b)+(c-d) by ring,add_mul]
  exact (abs_add_le ..).trans (add_le_add h.change g.change)
private theorem negE {δ a b m l : ℝ} (h : Env δ a b m l) : Env δ (-a) (-b) m l := by
  refine ⟨by simpa using h.left,by simpa using h.right,?_⟩
  rw [show -a-(-b)= -(a-b) by ring,abs_neg];exact h.change
private theorem mulE {δ a b c d m l n k : ℝ} (h : Env δ a b m l) (g : Env δ c d n k) :
    Env δ (a*c) (b*d) (m*n) (m*k+l*n) := by
  have mn := (abs_nonneg _).trans h.left
  refine ⟨?_,?_,?_⟩
  · rw [abs_mul];exact mul_le_mul h.left g.left (abs_nonneg _) mn
  · rw [abs_mul];exact mul_le_mul h.right g.right (abs_nonneg _) mn
  · rw [show a*c-b*d=a*(c-d)+(a-b)*d by ring]
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_mul]
    have x := mul_le_mul h.left g.change (abs_nonneg _) mn
    have y := mul_le_mul h.change g.right (abs_nonneg _) ((abs_nonneg _).trans h.change)
    linarith only [x,y]

private theorem finishE {δ a b m l : ℝ} (h : Env δ a b m l) (hl : l≤40) (hd : 0≤δ) :
    |a-b|≤40*δ := h.change.trans (mul_le_mul_of_nonneg_right hl hd)

def Box (x : Aug) : Prop := (∀i : Fin 6,i.val<5 → |x.1 i|≤10) ∧ (∀j i,|x.2 j i|≤2)
def Inner (x : Aug) : Prop := (∀i : Fin 6,i.val<5 → |x.1 i|≤9) ∧ (∀j i,|x.2 j i|≤1)

theorem state_diff (x y : Aug) (i : Fin 6) : |x.1 i-y.1 i|≤‖x-y‖ :=
  (coordinate_bound (x.1-y.1) i).trans (norm_fst_le (x-y))
theorem variation_diff (x y : Aug) (j : Fin 5) (i : Fin 6) : |x.2 j i-y.2 j i|≤‖x-y‖ :=
  ((coordinate_bound (x.2 j-y.2 j) i).trans (norm_le_pi_norm (x.2-y.2) j)).trans (norm_snd_le (x-y))

private theorem subE {δ a b c d m l n k : ℝ} (h : Env δ a b m l) (g : Env δ c d n k) :
    Env δ (a-c) (b-d) (m+n) (l+k) := by simpa only [sub_eq_add_neg] using plusE h (negE g)
private theorem divE {δ a b m l : ℝ} (h : Env δ a b m l) (d : ℝ) :
    Env δ (a/d) (b/d) (m*|d⁻¹|) (m*0+l*|d⁻¹|) := by
  simpa only [div_eq_mul_inv] using mulE h (constant δ d⁻¹)
private theorem squareE {δ a b m l : ℝ} (h : Env δ a b m l) :
    Env δ (a^2) (b^2) (m*m) (m*l+l*m) := by simpa only [pow_two] using mulE h h
private theorem cubeE {δ a b m l : ℝ} (h : Env δ a b m l) :
    Env δ (a^3) (b^3) ((m*m)*m) ((m*m)*l+(m*l+l*m)*m) := by
  simpa only [pow_succ, pow_zero,one_mul] using mulE (squareE h) h

theorem augmented_lipschitz (x y : Aug) (hx : Box x) (hy : Box y) :
    ‖augmented x-augmented y‖≤40*‖x-y‖ := by
  have bx (i : Fin 6) (hi : i.val<5) : Env ‖x-y‖ (x.1 i) (y.1 i) 10 1 :=
    ⟨hx.1 i hi,hy.1 i hi,by simpa using state_diff x y i⟩
  have bycol (j : Fin 5) (i : Fin 6) : Env ‖x-y‖ (x.2 j i) (y.2 j i) 2 1 :=
    ⟨hx.2 j i,hy.2 j i,by simpa using variation_diff x y j i⟩
  rw [Prod.norm_def,max_le_iff]
  constructor
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    change |Rotating.field x.1 i-Rotating.field y.1 i|≤_
    fin_cases i
    · exact finishE (mulE (constant _ 8) (bx 1 (by decide))) (by norm_num) (norm_nonneg _)
    · exact finishE (subE (subE (divE (negE (cubeE (bx 0 (by decide)))) 16) (divE (bx 2 (by decide)) 8)) (divE (mulE (bx 4 (by decide)) (bx 3 (by decide))) 8)) (by norm_num) (norm_nonneg _)
    · exact finishE (mulE (negE (bx 0 (by decide))) (bx 3 (by decide))) (by norm_num) (norm_nonneg _)
    · exact finishE (plusE (constant _ 1) (mulE (bx 0 (by decide)) (bx 2 (by decide)))) (by norm_num) (norm_nonneg _)
    · exact finishE (constant _ 0) (by norm_num) (norm_nonneg _)
    · exact finishE (bx 0 (by decide)) (by norm_num) (norm_nonneg _)
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    change |linear x.1 (x.2 j) i-linear y.1 (y.2 j) i|≤_
    fin_cases i
    · exact finishE (mulE (constant _ 8) (bycol j 1)) (by norm_num) (norm_nonneg _)
    · exact finishE (subE (subE (subE (divE (mulE (mulE (negE (constant _ 3)) (squareE (bx 0 (by decide)))) (bycol j 0)) 16) (divE (bycol j 2) 8)) (divE (mulE (bx 4 (by decide)) (bycol j 3)) 8)) (divE (mulE (bycol j 4) (bx 3 (by decide))) 8)) (by norm_num) (norm_nonneg _)
    · exact finishE (subE (mulE (negE (bx 0 (by decide))) (bycol j 3)) (mulE (bycol j 0) (bx 3 (by decide)))) (by norm_num) (norm_nonneg _)
    · exact finishE (plusE (mulE (bx 0 (by decide)) (bycol j 2)) (mulE (bycol j 0) (bx 2 (by decide)))) (by norm_num) (norm_nonneg _)
    · exact finishE (constant _ 0) (by norm_num) (norm_nonneg _)
    · exact finishE (bycol j 0) (by norm_num) (norm_nonneg _)

end
end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.augmented_lipschitz
