import SolitonClassification.Rotating.ResetCompactCell
import SolitonClassification.Rotating.ResetFastNode
namespace SolitonClassification.Rotating.DyadicReset
structure TapeRow (n : ℤ) where
  input : PackedCell
  left : Node
  right : Node
  inverse : Node
  stateVar : SignedCheck n (packedData input)
  bounded : Small (packedData input)
  endpoints : sampleStart input=left ∧ sampleEnd input=right
  invertible : CheckedNode left inverse

noncomputable def assemble {n : ℤ} {N : ℕ} (rows : ℕ→TapeRow n)
    (links : ∀i,i+1<N → (rows i).right=(rows (i+1)).left) : PolynomialTape n N :=
  {data := fun i=>packedData (rows i).input
   node := fun i=>(rows i).left
   inverse := fun i=>(rows i).inverse
   residual := fun i _=>(rows i).stateVar
   small := fun i _=>(rows i).bounded
   initial := fun i _ j=>by rw [packed_head,(rows i).endpoints.1]
   inverse_ok := fun i _=>(rows i).invertible
   matched := fun i hi j=>by rw [packed_sum,packed_head,(rows i).endpoints.2,links i hi,(rows (i+1)).endpoints.1]}
end SolitonClassification.Rotating.DyadicReset
