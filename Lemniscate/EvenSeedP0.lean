import Lemniscate.EvenSeedInputs

namespace Lemniscate.CoarseArithmetic
def evenSeedP0Computed : Matrix (Fin 31) (Fin 31) Interval := headAnchorProjectionInput 18 (evenSeedVectorData 2)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem even_seed_p0_comparison : ∀ i j,
    Encloses (evenSeedP0Matrix i j) (evenSeedP0Computed i j) := by
  unfold Encloses
  decide +kernel
theorem even_seed_p0_sound : MatrixContains evenSeedP0Matrix (Lemniscate.realFiniteAnchorProjection) := by
  have h : MatrixContains evenSeedP0Computed (Lemniscate.realFiniteAnchorProjection) := head_anchor_projection_input_sound 18 _ _ even_seed_anchor_sound
  intro i j
  exact (h i j).mono (even_seed_p0_comparison i j).1 (even_seed_p0_comparison i j).2
end Lemniscate.CoarseArithmetic
