import Lemniscate.IntervalSoundness
import Mathlib.Analysis.Real.Sqrt

/-! The positive reciprocal and certified square-root steps used when
normalizing the adjoint trial. No computed square root is trusted. -/
namespace Lemniscate.CoarseArithmetic

def reciprocalPositive (I : Interval) : Interval := ⟨1/I.hi, 1/I.lo⟩
def dividePositive (I J : Interval) : Interval := mul I (reciprocalPositive J)

theorem reciprocalPositive_sound (I : Interval) (x : ℝ)
    (hlo : 0 < I.lo) (hx : Contains I x) :
    Contains (reciprocalPositive I) (1/x) := by
  have hl : 0 < (I.lo:ℝ) := by exact_mod_cast hlo
  have hp : 0 < x := hl.trans_le hx.1
  constructor <;> simp only [reciprocalPositive, Rat.cast_div, Rat.cast_one]
  · exact one_div_le_one_div_of_le hp hx.2
  · exact one_div_le_one_div_of_le hl hx.1

theorem dividePositive_sound (I J : Interval) (x y : ℝ)
    (hlo : 0 < J.lo) (hx : Contains I x) (hy : Contains J y) :
    Contains (dividePositive I J) (x/y) := by
  simpa only [dividePositive, one_div, div_eq_mul_inv, one_mul] using
    mul_sound I (reciprocalPositive J) x (1/y) hx (reciprocalPositive_sound J y hlo hy)

theorem sqrt_enclosure_sound (I : Interval) (x : ℝ) (lo hi : ℚ)
    (hx : Contains I x) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hls : lo^2 ≤ I.lo) (hhs : I.hi ≤ hi^2) :
    Contains ⟨lo,hi⟩ (Real.sqrt x) := by
  have hl : 0 ≤ (lo:ℝ) := by exact_mod_cast hlo
  have hh : 0 ≤ (hi:ℝ) := by exact_mod_cast hhi
  have hls' : (lo:ℝ)^2 ≤ x := (by exact_mod_cast hls : (lo:ℝ)^2 ≤ (I.lo:ℝ)).trans hx.1
  have hhs' : x ≤ (hi:ℝ)^2 := hx.2.trans (by exact_mod_cast hhs)
  have hx0 : 0 ≤ x := (sq_nonneg (lo:ℝ)).trans hls'
  have hs := Real.sq_sqrt hx0
  have hs0 := Real.sqrt_nonneg x
  constructor <;> dsimp <;> nlinarith

theorem coarse_sqrt_two : Contains ⟨707/500,283/200⟩ (Real.sqrt 2) := by
  apply sqrt_enclosure_sound (point 2) 2 (707/500) (283/200) (point_sound 2)
  all_goals norm_num [point]

end Lemniscate.CoarseArithmetic
