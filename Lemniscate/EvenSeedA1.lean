import Lemniscate.EvenSeedInputs

namespace Lemniscate.CoarseArithmetic
def evenSeedA1Computed : Matrix (Fin 31) (Fin 31) Interval := finiteBlochCoefficientInput 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem even_seed_a1_comparison : ∀ i j,
    Encloses (evenSeedA1Matrix i j) (evenSeedA1Computed i j) := by
  unfold Encloses
  decide +kernel
theorem even_seed_a1_sound : MatrixContains evenSeedA1Matrix (Lemniscate.evenBlochCoefficientMatrix lemniscateFrequencySquared nome 1) := by
  have h : MatrixContains evenSeedA1Computed (Lemniscate.evenBlochCoefficientMatrix lemniscateFrequencySquared nome 1) := finite_bloch_coefficient_input_sound 1
  intro i j
  exact (h i j).mono (even_seed_a1_comparison i j).1 (even_seed_a1_comparison i j).2
end Lemniscate.CoarseArithmetic
