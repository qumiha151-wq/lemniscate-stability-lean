import Lemniscate.EvenSeedInputs

namespace Lemniscate.CoarseArithmetic
def evenSeedA2Computed : Matrix (Fin 31) (Fin 31) Interval := finiteBlochCoefficientInput 2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem even_seed_a2_comparison : ∀ i j,
    Encloses (evenSeedA2Matrix i j) (evenSeedA2Computed i j) := by
  unfold Encloses
  decide +kernel
theorem even_seed_a2_sound : MatrixContains evenSeedA2Matrix (Lemniscate.evenBlochCoefficientMatrix lemniscateFrequencySquared nome 2) := by
  have h : MatrixContains evenSeedA2Computed (Lemniscate.evenBlochCoefficientMatrix lemniscateFrequencySquared nome 2) := finite_bloch_coefficient_input_sound 2
  intro i j
  exact (h i j).mono (even_seed_a2_comparison i j).1 (even_seed_a2_comparison i j).2
end Lemniscate.CoarseArithmetic
