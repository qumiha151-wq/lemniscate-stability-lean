import Lemniscate.EvenSeedInputs
import Lemniscate.EvenSeedP0

namespace Lemniscate.CoarseArithmetic
def evenSeedPComputed : Matrix (Fin 31) (Fin 31) Interval :=
  intervalMatrixAdd headDeltaInput (intervalMatrixNeg evenSeedP0Matrix)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem even_seed_p_comparison : ∀ i j,
    Encloses (evenSeedPMatrix i j) (evenSeedPComputed i j) := by
  unfold Encloses
  decide +kernel
theorem even_seed_p_sound : MatrixContains evenSeedPMatrix Lemniscate.realFiniteStableProjection := by
  have hId : MatrixContains headDeltaInput (1 : Matrix (Fin 31) (Fin 31) ℝ) := by
    intro i j
    change Contains (headDeltaInput i j) (if i = j then (1:ℝ) else 0)
    exact head_delta_input_sound i j
  have h := interval_matrix_add_sound _ _ _ _ hId
    (interval_matrix_neg_sound _ _ even_seed_p0_sound)
  have h' : MatrixContains evenSeedPComputed Lemniscate.realFiniteStableProjection := by
    simpa only [evenSeedPComputed, Lemniscate.realFiniteStableProjection, sub_eq_add_neg] using h
  intro i j
  exact (h' i j).mono (even_seed_p_comparison i j).1 (even_seed_p_comparison i j).2
end Lemniscate.CoarseArithmetic
