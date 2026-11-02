import Lemniscate.EvenMatrixSeedData
import Lemniscate.FiniteCoefficientIntervals

namespace Lemniscate.CoarseArithmetic
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem even_seed_input_comparisons :
    (∀ i, Encloses (evenSeedVectorData 0 i) (finiteRotationInput i)) ∧
    (∀ i, Encloses (evenSeedVectorData 1 i) (finiteAdjointInput i)) ∧
    (∀ i, Encloses (evenSeedVectorData 2 i) (finiteAnchorInput i)) ∧
    Encloses evenSeedDenData finiteHouseholderDenInput ∧ 0 < evenSeedDenData.lo := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem even_seed_rotation_sound (i : Fin 31) :
    Contains (evenSeedVectorData 0 i) (Lemniscate.finiteRotationHead i) :=
  (finite_rotation_input_sound i).mono (even_seed_input_comparisons.1 i).1
    (even_seed_input_comparisons.1 i).2
theorem even_seed_adjoint_sound (i : Fin 31) :
    Contains (evenSeedVectorData 1 i) (Lemniscate.finiteAdjointHead i) :=
  (finite_adjoint_input_sound i).mono (even_seed_input_comparisons.2.1 i).1
    (even_seed_input_comparisons.2.1 i).2
theorem even_seed_anchor_sound (i : Fin 31) :
    Contains (evenSeedVectorData 2 i) (Lemniscate.finiteAnchorHead i) :=
  (finite_anchor_input_sound i).mono (even_seed_input_comparisons.2.2.1 i).1
    (even_seed_input_comparisons.2.2.1 i).2
theorem even_seed_den_sound : Contains evenSeedDenData
    (1+∑ i : Fin 31, Lemniscate.finiteRotationHead i*Lemniscate.finiteAnchorHead i) :=
  finite_householder_den_input_sound.mono even_seed_input_comparisons.2.2.2.1.1
    even_seed_input_comparisons.2.2.2.1.2
end Lemniscate.CoarseArithmetic
