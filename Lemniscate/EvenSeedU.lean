import Lemniscate.EvenSeedInputs

namespace Lemniscate.CoarseArithmetic
def evenSeedUComputed : Matrix (Fin 31) (Fin 31) Interval := headHouseholderInput 18 (evenSeedVectorData 0) (evenSeedVectorData 2) evenSeedDenData
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem even_seed_u_comparison : ∀ i j,
    Encloses (evenSeedUMatrix i j) (evenSeedUComputed i j) := by
  unfold Encloses
  decide +kernel
theorem even_seed_u_sound : MatrixContains evenSeedUMatrix (Lemniscate.realFiniteHouseholder) := by
  have h : MatrixContains evenSeedUComputed (Lemniscate.realFiniteHouseholder) := head_householder_input_sound 18 _ _ _ _ _ even_seed_rotation_sound even_seed_anchor_sound even_seed_den_sound even_seed_input_comparisons.2.2.2.2
  intro i j
  exact (h i j).mono (even_seed_u_comparison i j).1 (even_seed_u_comparison i j).2
end Lemniscate.CoarseArithmetic
