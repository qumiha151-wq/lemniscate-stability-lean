import Lemniscate.ShortSchurHighArithmetic

/-! Exact rational upper bounds displayed in the manuscript's five-row table.
The coupling and finite high-row quantities already include their infinite tails.
All comparisons reduce the current integer interval certificates in the kernel. -/
namespace Lemniscate.CoarseArithmetic

def shortSummaryLowUpper : Fin 5 → ℚ :=
  ![-1237/10000, -1166/10000, -1257/10000, -1251/10000, -860/10000]

def shortSummaryCrossUpper : Fin 5 → ℚ :=
  ![5645/100000, 5652/100000, 5685/100000, 5744/100000, 5828/100000]

def shortSummaryHighUpper : Fin 5 → ℚ :=
  ![-16210/10000, -15845/10000, -14997/10000, -13964/10000, -12998/10000]

/-- Outward-rounded off-diagonal bounds in the displayed second-row example.
The diagonal slot is unused. Indices are numbered from zero. -/
def shortExampleRowAbsUpper : Fin 7 → ℚ :=
  ![7269/10000, 0, 3262/10000, 526/10000, 1/10000, 2694/10000, 1/10000]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem short_certificate_summary :
    (∀ (j : Fin 5) (i : Fin 7), shortLowRowUpper j i < shortSummaryLowUpper j) ∧
    (∀ j : Fin 5, shortFiniteCrossSquare j + shortCrossTailSquare <
      shortSummaryCrossUpper j) ∧
    (∀ (j : Fin 5) (i : Fin 22), shortFiniteHighRow j i < shortSummaryHighUpper j) ∧
    (shortC0Data 1 1).toInterval.hi ≤ -(2939/10000 : ℚ) ∧
    (∀ k : Fin 7, k ≠ 1 →
      absUpper (shortC0Data 1 k).toInterval ≤ shortExampleRowAbsUpper k) ∧
    (-(2939/10000 : ℚ) + ∑ k : Fin 7, if k = 1 then 0 else
      shortExampleRowAbsUpper k * (shortLowWeight 0 k / shortLowWeight 0 1)) =
        -(1302249/10000000 : ℚ) ∧
    -(1302249/10000000 : ℚ) < -(2/25 : ℚ) := by
  decide +kernel

end Lemniscate.CoarseArithmetic
