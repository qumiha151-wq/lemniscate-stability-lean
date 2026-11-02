import Lemniscate.EvenSeedInputs

namespace Lemniscate.CoarseArithmetic
def evenSeedA0Computed : Matrix (Fin 31) (Fin 31) Interval := finiteBlochCoefficientInput 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem even_seed_a0_comparison : ∀ i j,
    Encloses (evenSeedA0Matrix i j) (evenSeedA0Computed i j) := by
  unfold Encloses
  decide +kernel
theorem even_seed_a0_sound : MatrixContains evenSeedA0Matrix (Lemniscate.evenBlochCoefficientMatrix thetaParameter nome 0) := by
  have h : MatrixContains evenSeedA0Computed (Lemniscate.evenBlochCoefficientMatrix thetaParameter nome 0) := finite_bloch_coefficient_input_sound 0
  intro i j
  exact (h i j).mono (even_seed_a0_comparison i j).1 (even_seed_a0_comparison i j).2
end Lemniscate.CoarseArithmetic
