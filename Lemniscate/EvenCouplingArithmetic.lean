import Lemniscate.CoarseArithmetic

/-! Coarse rational constants for the proposed analytic coupling estimate.
These inequalities alone do not assert the operator coupling bound. -/
namespace Lemniscate.CoarseArithmetic

def evenAnalyticBaseUpper : ℚ :=
  (3/8)*4*6^2*sumTo 4 (fun j => tail2 (qb^2) (j+1))+
  62*6^2*15000*tail2 (qb^2) 5

def evenLowTestTailSquareUpper : ℚ := 2*1800^2*tail2 (qb^2) 6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem even_analytic_coupling_constants :
    evenAnalyticBaseUpper < 1/9 ∧
    evenLowTestTailSquareUpper ≤ (1/8000)^2 ∧
    (2*((1/8000)^2+(1/51200)^2):ℚ) ≤ (1/5000)^2 ∧
    ((11/10)*(1/9)+11*(75/5000)^2:ℚ) ≤ 1/8 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Lemniscate.CoarseArithmetic
