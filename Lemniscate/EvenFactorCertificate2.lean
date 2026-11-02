import Lemniscate.EvenFactorData

namespace Lemniscate.CoarseArithmetic
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem even_factor_certificate_2 :
    (∀ i : Fin 31, 0 ≤ evenFactorDiagonal 2 i) ∧
      (∀ i : Fin 31, evenFactorRowBound 2 i ≤ 1) := by
  constructor <;> decide +kernel
end Lemniscate.CoarseArithmetic
