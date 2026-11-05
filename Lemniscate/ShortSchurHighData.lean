import Lemniscate.CoarseArithmetic

/-! The common rational constants in the high-frequency estimates.
All moments include their complete infinite geometric tails. -/
namespace Lemniscate.CoarseArithmetic

def shortHighOffCoefficient : ℚ :=
  rhi*H*(45*(17/16:ℚ)^2/64+(15/4:ℚ)*(1/4:ℚ)^2)

def shortCrossTailSquare : ℚ :=
  14*10^12*H^2/qb^14*
    (tail2 (qb^2) 15+14*tail1 (qb^2) 15+49*(qb^2)^15/(1-qb^2))

def shortInsideRowTail : ℚ :=
  2*10^6*H/qb^7*(tail1 qb 15+7*qb^15/(1-qb))

def shortRawHighRow : ℚ :=
  -4*rlo^2*(1-1/60:ℚ)^4+45*rhi*(1+1/60:ℚ)^2/900+
    2*shortHighOffCoefficient*moment 1 qb

def shortFiniteRankHighTail : ℚ := 8*10^6*H*22*qb^8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem short_high_tail_arithmetic :
    shortCrossTailSquare < 4437/10^8 ∧
    shortInsideRowTail < 3728/10^6 ∧
    shortRawHighRow+shortFiniteRankHighTail < -(5/4:ℚ) := by
  decide +kernel

end Lemniscate.CoarseArithmetic
