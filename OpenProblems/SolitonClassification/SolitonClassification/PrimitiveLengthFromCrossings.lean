import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Arithmetic consequences of the ordered-label-pair and chart bounds
in the written proof of CrossingComplexity. Here L is the normalized
primitive arclength and N counts distinct image points with two or more
preimages, including ordinary transverse double points. -/
noncomputable section
namespace ClosedSimilarity.CrossingLength

private theorem root_pow (x : ℝ) (hx : 0≤x) (n : ℕ) (hn : n≠0) :
    (x ^ ((1:ℝ)/n)) ^ n = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx,one_div,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn),Real.rpow_one]

/-- Each distinct multiple point contributes at least two ordered pairs.
    The elementary sixth-root lower bound follows from that pair count. -/
theorem sixth_root_lower {L : ℝ} (N : ℕ) (hl : 0≤L)
    (ordered : 2*(N:ℝ)≤3*(1+2^24*L*(1+L)^2)^2) :
    (2*(N:ℝ)/3)^((1:ℝ)/6)/256 - 2/3 ≤ L := by
  let a := 1+2^24*L*(1+L)^2
  let b := 256*(L+2/3)
  have apos : 0≤a := by dsimp [a]; positivity
  have bpos : 0≤b := by dsimp [b]; positivity
  have ab : a≤b^3 := by dsimp [a,b]; nlinarith only [hl]
  have counts : 2*(N:ℝ)/3 ≤ b^6 := by
    calc
      _ ≤ a^2 := by dsimp [a]; linarith only [ordered]
      _ ≤ (b^3)^2 := pow_le_pow_left₀ apos ab 2
      _ = _ := by ring
  let x := (2*(N:ℝ)/3)^((1:ℝ)/6)
  have hx : x^6=2*(N:ℝ)/3 := root_pow _ (by positivity) 6 (by decide)
  have xb : x≤b := by
    by_contra! bad
    exact (not_lt_of_ge counts) (by rw [← hx]; exact pow_lt_pow_left₀ bad bpos (by decide))
  change x/256-2/3 ≤ L
  dsimp [b] at xb
  linarith

/-- Retaining the distinct chart-pair count yields a positive inverse
    bound even when N is small. The chart count is the ceiling of the
    normalized length divided by the short-chart size. -/
theorem positive_chart_lower {L : ℝ} {N m : ℕ} (hl : 0<L) (hN : 0<N) (hm : 0<m)
    (chart : (m:ℝ)-1 < 2^24*L*(1+L)^2)
    (ordered : 2*(N:ℝ)≤3*(m:ℝ)*((m:ℝ)-1)) :
    let u := (Real.sqrt (1+8*(N:ℝ)/3)-1)/(2*2^24)
    0 < u/(1+u^((1:ℝ)/3))^2 ∧ u/(1+u^((1:ℝ)/3))^2 < L := by
  let x := 2^24*L*(1+L)^2
  let u := (Real.sqrt (1+8*(N:ℝ)/3)-1)/(2*2^24)
  let c := u^((1:ℝ)/3)
  have npos : (0:ℝ)<N := by exact_mod_cast hN
  have mone : (1:ℝ)≤m := by exact_mod_cast hm
  have sq := Real.sq_sqrt (show 0≤1+8*(N:ℝ)/3 by positivity)
  have nn := Real.sqrt_nonneg (1+8*(N:ℝ)/3)
  have large : 1 < Real.sqrt (1+8*(N:ℝ)/3) := by nlinarith
  have up : 0<u := by dsimp [u]; positivity
  have cp : 0<c := Real.rpow_pos_of_pos up _
  have cube : c^3 = u := root_pow u up.le 3 (by decide)
  have before : (m:ℝ)-1<x := chart
  have after : (m:ℝ)<1+x := by linarith
  have xp : 0<x := by dsimp [x]; positivity
  have product : (m:ℝ)*((m:ℝ)-1) < (1+x)*x :=
    (mul_le_mul_of_nonneg_right after.le (by linarith)).trans_lt
      (mul_lt_mul_of_pos_left before (by linarith))
  have radical : Real.sqrt (1+8*(N:ℝ)/3) < 1+2*x := by
    by_contra! h
    have sqle := pow_le_pow_left₀ (show 0≤1+2*x by positivity) h 2
    nlinarith only [sq,sqle,ordered,product]
  have ub : u<L*(1+L)^2 := by dsimp [u]; dsimp [x] at radical; linarith
  change 0<u/(1+c)^2 ∧ u/(1+c)^2<L
  refine ⟨by positivity,(div_lt_iff₀ (by positivity)).mpr ?_⟩
  rcases le_or_gt L c with lc | lc
  · exact ub.trans_le (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) 2) hl.le)
  · have strict : c^2<(1+c)^2 := by nlinarith only [cp]
    calc
      u = c*c^2 := by rw [← cube]; ring
      _ < c*(1+c)^2 := mul_lt_mul_of_pos_left strict cp
      _ ≤ L*(1+c)^2 := mul_le_mul_of_nonneg_right lc.le (sq_nonneg _)

end ClosedSimilarity.CrossingLength
#print axioms ClosedSimilarity.CrossingLength.sixth_root_lower
#print axioms ClosedSimilarity.CrossingLength.positive_chart_lower
