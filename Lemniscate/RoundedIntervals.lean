import Lemniscate.IntervalExtras
import Mathlib.Data.Rat.Floor

/-! Outward rounding to a fixed decimal denominator. Every rounded interval
contains the exact rational interval, so the subsequent finite certificates
can use bounded integer sizes without trusting floating-point arithmetic. -/
namespace Lemniscate.CoarseArithmetic

def roundInterval (digits : ℕ) (I : Interval) : Interval :=
  ⟨(⌊I.lo*(10:ℚ)^digits⌋ : ℚ)/(10:ℚ)^digits,
   (⌈I.hi*(10:ℚ)^digits⌉ : ℚ)/(10:ℚ)^digits⟩

theorem roundInterval_sound (digits : ℕ) (I : Interval) (x : ℝ)
    (hx : Contains I x) : Contains (roundInterval digits I) x := by
  apply hx.mono
  · change (⌊I.lo*(10:ℚ)^digits⌋ : ℚ)/(10:ℚ)^digits ≤ I.lo
    exact (div_le_iff₀ (by positivity)).mpr (Int.floor_le _)
  · change I.hi ≤ (⌈I.hi*(10:ℚ)^digits⌉ : ℚ)/(10:ℚ)^digits
    exact (le_div_iff₀ (by positivity)).mpr (Int.le_ceil _)

end Lemniscate.CoarseArithmetic
