import Lemniscate.IntervalSoundness
import Mathlib.Tactic.Positivity

/-! Monotonicity and exact coarse enclosures for the positive even Fourier
coefficient formula. Identification with the Jacobi function's Fourier series
and the transcendental bounds on its parameters remain separate obligations. -/
namespace Lemniscate.CoarseArithmetic

noncomputable def evenCoefficient (r q : ℝ) (j : ℕ) : ℝ :=
  8*r*(j:ℝ)*q^j/(1-q^(2*j))

theorem evenCoefficient_mono (r s q t : ℝ) (j : ℕ)
    (hr : 0 ≤ r) (hrs : r ≤ s) (hq : 0 ≤ q) (hqt : q ≤ t)
    (ht : t < 1) (hj : 0 < j) :
    evenCoefficient r q j ≤ evenCoefficient s t j := by
  have hs : 0 ≤ s := hr.trans hrs
  have ht0 : 0 ≤ t := hq.trans hqt
  have hpow := pow_le_pow_left₀ hq hqt j
  have hpow2 := pow_le_pow_left₀ hq hqt (2*j)
  have hden : 0 < 1-t^(2*j) := sub_pos.mpr
    (pow_lt_one₀ ht0 ht (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hj)))
  have hnum : 8*r*(j:ℝ)*q^j ≤ 8*s*(j:ℝ)*t^j := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrs (by norm_num)) (Nat.cast_nonneg j)
    · exact hpow
    · exact pow_nonneg hq j
    · positivity
  exact div_le_div₀ (by positivity) hnum hden (sub_le_sub_left hpow2 1)

theorem positive_fourier_enclosure (r q : ℝ) (j : ℕ)
    (hr : Contains ⟨rlo,rhi⟩ r) (hq : Contains ⟨qlo,qhi⟩ q) (hj : 0 < j) :
    Contains (hInterval j) (evenCoefficient r q j) := by
  have hr0 : 0 ≤ r := (by norm_num [rlo] : (0:ℝ) ≤ (rlo:ℝ)).trans hr.1
  have hq0 : 0 ≤ q := (by norm_num [qlo] : (0:ℝ) ≤ (qlo:ℝ)).trans hq.1
  have hq1 : q < 1 := hq.2.trans_lt (by norm_num [qhi])
  have hl := evenCoefficient_mono (rlo:ℝ) r (qlo:ℝ) q j
    (by norm_num [rlo]) hr.1 (by norm_num [qlo]) hq.1 hq1 hj
  have hu := evenCoefficient_mono r (rhi:ℝ) q (qhi:ℝ) j
    hr0 hr.2 hq0 hq.2 (by norm_num [qhi]) hj
  constructor
  · simpa [hInterval, hLower, Nat.ne_of_gt hj, hLowerPositive, evenCoefficient] using hl
  · simpa [hInterval, hUpper, Nat.ne_of_gt hj, hUpperPositive, evenCoefficient] using hu

end Lemniscate.CoarseArithmetic
