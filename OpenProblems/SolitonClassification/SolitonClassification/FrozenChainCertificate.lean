import SolitonClassification.FrozenPackedRow
import SolitonClassification.FrozenDyadicChain

/-! A certificate binds every polynomial's starting and ending marks, the
entire error budget, and the exact endpoint of the final row. -/
namespace ClosedSimilarity.FrozenStress.Endpoint

def rowAt (rows : List Row) (i : ℕ) : Row := rows[i]?.getD ⟨[],[],[],[]⟩

theorem checked_transport (r : Row) (i : ℕ) (a b : Mark) (hi : i<640)
    (check : PackedGood r ∧ startMark r=a ∧ finishMark r=b) :
    Transports i (i+1) a b := by
  rw [←check.2.1,←check.2.2]
  exact transport_one r i hi (packed_good_sound r check.1)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.checked_transport
