import Lemniscate.EvenSeedInputs

namespace Lemniscate.CoarseArithmetic
def evenSeedTComputed : Matrix (Fin 31) (Fin 31) Interval := headNeutralInput 18 (evenSeedVectorData 0) (evenSeedVectorData 1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem even_seed_t_comparison : ∀ i j,
    Encloses (evenSeedTMatrix i j) (evenSeedTComputed i j) := by
  unfold Encloses
  decide +kernel
theorem even_seed_t_sound : MatrixContains evenSeedTMatrix (Lemniscate.realFiniteNeutral) := by
  have h : MatrixContains evenSeedTComputed (Lemniscate.realFiniteNeutral) := head_neutral_input_sound 18 _ _ _ _ even_seed_rotation_sound even_seed_adjoint_sound
  intro i j
  exact (h i j).mono (even_seed_t_comparison i j).1 (even_seed_t_comparison i j).2
end Lemniscate.CoarseArithmetic
