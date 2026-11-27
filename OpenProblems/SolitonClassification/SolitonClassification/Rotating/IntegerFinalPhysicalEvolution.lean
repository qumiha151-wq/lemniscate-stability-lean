import SolitonClassification.Rotating.IntegerPhysicalGenerator
import SolitonClassification.Rotating.ResetCompletePlus
import SolitonClassification.Rotating.ResetCompleteMinus

namespace SolitonClassification.Rotating.IntegerTarget.Physical
open DyadicReset

theorem exists_actual_primitive_rotating_flow : ∃P : Seed, PrimitiveEvolution P :=
  physical_evolution_of_indexed_rows CompletePlus.atRow CompleteMinus.atRow
    CompletePlus.range CompleteMinus.range

end SolitonClassification.Rotating.IntegerTarget.Physical
#print axioms SolitonClassification.Rotating.IntegerTarget.Physical.exists_actual_primitive_rotating_flow
