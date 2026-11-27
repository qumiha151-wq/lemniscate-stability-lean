import SolitonClassification.Rotating.IntegerTerminalRows
import Mathlib.Analysis.Convex.Combination

namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
open Set
set_option maxHeartbeats 1200000

def oriented (u v z : ℝ × ℝ) : ℝ :=
  (u.1-z.1)*(v.2-z.2)-(u.2-z.2)*(v.1-z.1)

/-- The three normalized oriented areas give a convex combination for z. -/
theorem hull_of_oriented_areas {S : Set (ℝ × ℝ)} {a b r z : ℝ × ℝ}
    (ha : a∈S) (hb : b∈S) (hr : r∈S)
    (hab : 0<oriented a b z) (hbr : 0<oriented b r z) (hra : 0<oriented r a z) :
    z∈convexHull ℝ S := by
  let D := oriented b r z + oriented r a z + oriented a b z
  have Dp : 0<D := by dsimp [D]; positivity
  let w : Fin 3→ℝ := ![oriented b r z/D,oriented r a z/D,oriented a b z/D]
  let points : Fin 3→ℝ×ℝ := ![a,b,r]
  have wn (i : Fin 3) : 0≤w i := by fin_cases i <;> dsimp [w] <;> positivity
  have ws : ∑i,w i=1 := by
    rw [Fin.sum_univ_three]
    change oriented b r z/D+oriented r a z/D+oriented a b z/D=1
    rw [←add_div,←add_div,show oriented b r z+oriented r a z+oriented a b z=D from rfl,div_self Dp.ne']
  have mem (i : Fin 3) : points i∈convexHull ℝ S := by
    apply subset_convexHull
    fin_cases i <;> first | exact ha | exact hb | exact hr
  have hm := (convex_convexHull ℝ S).sum_mem (t:=Finset.univ) (w:=w) (z:=points)
    (fun i _ => wn i) ws (fun i _ => mem i)
  have recover : ∑i,w i • points i=z := by
    simp only [Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
    ext <;> dsimp [w,points] <;> field_simp [Dp.ne'] <;> dsimp [D,oriented] <;> ring
  rwa [recover] at hm

/-- Three coordinate boxes enclose a fixed square centered at zero.
Coordinates are in the physical similarity-center frame. -/
theorem fixed_square_of_three_boxes {S : Set (ℝ × ℝ)} {a b r : ℝ × ℝ}
    (ha : a∈S) (hb : b∈S) (hr : r∈S)
    (ax : a.1∈Icc (-(13/100)) (-(8/100))) (ay : a.2∈Icc (13/100) (19/100))
    (bx : b.1∈Icc (-(27/10)) (-(25/10))) (byv : b.2∈Icc (-(21/10)) (-(19/10)))
    (rx : r.1∈Icc 2 (22/10)) (ry : r.2∈Icc (6/10) (73/100)) :
    ∀z : ℝ × ℝ, |z.1|≤1/20 → |z.2|≤1/20 → z∈convexHull ℝ S := by
  intro z h1 h2
  obtain ⟨xl,xu⟩ := abs_le.mp h1
  obtain ⟨yl,yu⟩ := abs_le.mp h2
  have al : a.1-z.1<0 := by linarith [ax.2]
  have ap : 0<a.2-z.2 := by linarith [ay.1]
  have bl : b.1-z.1<0 := by linarith [bx.2]
  have bn : b.2-z.2<0 := by linarith [byv.2]
  have rp : 0<r.1-z.1 := by linarith [rx.1]
  have rq : 0<r.2-z.2 := by linarith [ry.1]
  apply hull_of_oriented_areas ha hb hr
  · unfold oriented
    linarith only [mul_pos_of_neg_of_neg al bn,mul_neg_of_pos_of_neg ap bl]
  · have lo : (18/10:ℝ)*(19/10) ≤ (z.2-b.2)*(r.1-z.1) :=
      mul_le_mul (by linarith [byv.2]) (by linarith [rx.1]) (by norm_num) (by linarith)
    have hi : (z.1-b.1)*(r.2-z.2) ≤ (28/10:ℝ)*(8/10) :=
      mul_le_mul (by linarith [bx.1]) (by linarith [ry.2]) rq.le (by norm_num)
    unfold oriented
    nlinarith only [lo,hi]
  · unfold oriented
    linarith only [mul_pos rp ap,mul_neg_of_pos_of_neg rq al]

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.fixed_square_of_three_boxes
