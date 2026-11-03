import Lemniscate.EvenSeedInputs

namespace Lemniscate.CoarseArithmetic
def evenSeedA3Computed : Matrix (Fin 31) (Fin 31) Interval := finiteBlochCoefficientInput 3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem even_seed_a3_comparison : ∀ i j,
    Encloses (evenSeedA3Matrix i j) (evenSeedA3Computed i j) := by
  unfold Encloses
  decide +kernel
theorem even_seed_a3_sound : MatrixContains evenSeedA3Matrix (Lemniscate.evenBlochCoefficientMatrix lemniscateFrequencySquared nome 3) := by
  have h : MatrixContains evenSeedA3Computed (Lemniscate.evenBlochCoefficientMatrix lemniscateFrequencySquared nome 3) := finite_bloch_coefficient_input_sound 3
  intro i j
  exact (h i j).mono (even_seed_a3_comparison i j).1 (even_seed_a3_comparison i j).2
end Lemniscate.CoarseArithmetic
