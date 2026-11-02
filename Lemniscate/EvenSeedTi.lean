import Lemniscate.EvenSeedInputs

namespace Lemniscate.CoarseArithmetic
def evenSeedTiComputed : Matrix (Fin 31) (Fin 31) Interval := headNeutralInvInput 18 (evenSeedVectorData 0) (evenSeedVectorData 1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem even_seed_ti_comparison : ∀ i j,
    Encloses (evenSeedTiMatrix i j) (evenSeedTiComputed i j) := by
  unfold Encloses
  decide +kernel
theorem even_seed_ti_sound : MatrixContains evenSeedTiMatrix (Lemniscate.realFiniteNeutralInv) := by
  have h : MatrixContains evenSeedTiComputed (Lemniscate.realFiniteNeutralInv) := head_neutral_inv_input_sound 18 _ _ _ _ even_seed_rotation_sound even_seed_adjoint_sound
  intro i j
  exact (h i j).mono (even_seed_ti_comparison i j).1 (even_seed_ti_comparison i j).2
end Lemniscate.CoarseArithmetic
