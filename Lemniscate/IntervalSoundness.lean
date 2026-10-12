import Lemniscate.Algebra
import Lemniscate.CoarseArithmetic
import Mathlib.Data.Rat.Cast.Order

/-! Real-number soundness of the executable rational interval operations. -/
namespace Lemniscate.CoarseArithmetic

def Contains (I : Interval) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

theorem point_sound (q : ℚ) : Contains (point q) (q : ℝ) := by
  exact ⟨le_rfl, le_rfl⟩

theorem add_sound (I J : Interval) (x y : ℝ)
    (hx : Contains I x) (hy : Contains J y) : Contains (add I J) (x+y) := by
  rcases hx with ⟨hxl,hxu⟩
  rcases hy with ⟨hyl,hyu⟩
  constructor <;> simp only [add, Rat.cast_add]
  · exact add_le_add hxl hyl
  · exact add_le_add hxu hyu

theorem real_mul_box (a b c d x y lo hi : ℝ)
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hl : lo ≤ a*c ∧ lo ≤ a*d ∧ lo ≤ b*c ∧ lo ≤ b*d)
    (hu : a*c ≤ hi ∧ a*d ≤ hi ∧ b*c ≤ hi ∧ b*d ≤ hi) :
    lo ≤ x*y ∧ x*y ≤ hi := by
  have hay : lo ≤ a*y ∧ a*y ≤ hi := by
    rcases le_total 0 a with ha | ha
    · exact ⟨hl.1.trans (mul_le_mul_of_nonneg_left hy.1 ha),
        (mul_le_mul_of_nonneg_left hy.2 ha).trans hu.2.1⟩
    · exact ⟨hl.2.1.trans (mul_le_mul_of_nonpos_left hy.2 ha),
        (mul_le_mul_of_nonpos_left hy.1 ha).trans hu.1⟩
  have hby : lo ≤ b*y ∧ b*y ≤ hi := by
    rcases le_total 0 b with hb | hb
    · exact ⟨hl.2.2.1.trans (mul_le_mul_of_nonneg_left hy.1 hb),
        (mul_le_mul_of_nonneg_left hy.2 hb).trans hu.2.2.2⟩
    · exact ⟨hl.2.2.2.trans (mul_le_mul_of_nonpos_left hy.2 hb),
        (mul_le_mul_of_nonpos_left hy.1 hb).trans hu.2.2.1⟩
  rcases le_total 0 y with hy0 | hy0
  · exact ⟨hay.1.trans (mul_le_mul_of_nonneg_right hx.1 hy0),
      (mul_le_mul_of_nonneg_right hx.2 hy0).trans hby.2⟩
  · exact ⟨hby.1.trans (mul_le_mul_of_nonpos_right hx.2 hy0),
      (mul_le_mul_of_nonpos_right hx.1 hy0).trans hay.2⟩

theorem mul_sound (I J : Interval) (x y : ℝ)
    (hx : Contains I x) (hy : Contains J y) : Contains (mul I J) (x*y) := by
  have hl : (mul I J).lo ≤ I.lo*J.lo ∧ (mul I J).lo ≤ I.lo*J.hi ∧
      (mul I J).lo ≤ I.hi*J.lo ∧ (mul I J).lo ≤ I.hi*J.hi := by
    simp [mul, min_le_iff]
  have hu : I.lo*J.lo ≤ (mul I J).hi ∧ I.lo*J.hi ≤ (mul I J).hi ∧
      I.hi*J.lo ≤ (mul I J).hi ∧ I.hi*J.hi ≤ (mul I J).hi := by
    simp [mul, le_max_iff]
  apply real_mul_box _ _ _ _ _ _ _ _ hx hy
  · exact_mod_cast hl
  · exact_mod_cast hu

theorem scale_sound (I : Interval) (x : ℝ) (q : ℚ) (hx : Contains I x) :
    Contains (scale I q) (x*(q:ℝ)) := mul_sound I (point q) x q hx (point_sound q)

theorem absUpper_sound (I : Interval) (x : ℝ) (hx : Contains I x) :
    |x| ≤ (absUpper I : ℝ) := by
  have hl : |(I.lo:ℝ)| ≤ (absUpper I : ℝ) := by
    exact_mod_cast (le_max_left |I.lo| |I.hi|)
  have hh : |(I.hi:ℝ)| ≤ (absUpper I : ℝ) := by
    exact_mod_cast (le_max_right |I.lo| |I.hi|)
  apply abs_le.mpr
  constructor
  · have h := neg_abs_le (I.lo:ℝ)
    linarith [hx.1]
  · exact hx.2.trans ((le_abs_self _).trans hh)

end Lemniscate.CoarseArithmetic
