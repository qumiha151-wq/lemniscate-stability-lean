import SolitonClassification.Rotating.ResetTilePlus00
import SolitonClassification.Rotating.ResetTilePlus01
import SolitonClassification.Rotating.ResetTilePlus02
import SolitonClassification.Rotating.ResetTilePlus03
import SolitonClassification.Rotating.ResetTilePlus04
import SolitonClassification.Rotating.ResetTilePlus05
import SolitonClassification.Rotating.ResetTilePlus06
import SolitonClassification.Rotating.ResetTilePlus07
import SolitonClassification.Rotating.ResetTilePlus08
import SolitonClassification.Rotating.ResetTilePlus09
namespace SolitonClassification.Rotating.DyadicReset.HullPlus
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def cellBlock : ℕ→ℕ→TapeRow Middle.hn
  | 0 => TilePlus00.atRow
  | 1 => TilePlus01.atRow
  | 2 => TilePlus02.atRow
  | 3 => TilePlus03.atRow
  | 4 => TilePlus04.atRow
  | 5 => TilePlus05.atRow
  | 6 => TilePlus06.atRow
  | 7 => TilePlus07.atRow
  | 8 => TilePlus08.atRow
  | 9 => TilePlus09.atRow
  | _ => TilePlus00.atRow
theorem indexes (b j : ℕ) (hb : b<10) (hj : j<64) :
    (cellBlock b j).left=GridPlus.atNode (64*b+j) ∧ (cellBlock b j).right=GridPlus.atNode (64*b+j+1) := by
  interval_cases b
  · exact TilePlus00.at_index j hj
  · exact TilePlus01.at_index j hj
  · exact TilePlus02.at_index j hj
  · exact TilePlus03.at_index j hj
  · exact TilePlus04.at_index j hj
  · exact TilePlus05.at_index j hj
  · exact TilePlus06.at_index j hj
  · exact TilePlus07.at_index j hj
  · exact TilePlus08.at_index j hj
  · exact TilePlus09.at_index j hj
def atRow (i : ℕ) := cellBlock (i/64) (i%64)
theorem range (i : ℕ) (hi : i<640) : (atRow i).left=GridPlus.atNode i ∧ (atRow i).right=GridPlus.atNode (i+1) := by
  have eq : 64*(i/64)+i%64=i := Nat.div_add_mod i 64
  have b := indexes (i/64) (i%64) (by omega) (Nat.mod_lt _ (by decide))
  simpa only [atRow,eq] using b
theorem links (i : ℕ) (hi : i+1<640) : (atRow i).right=(atRow (i+1)).left :=
  (range i (by omega)).2.trans (range (i+1) hi).1.symm
def tape : PolynomialTape Middle.hn 640 := assemble atRow links
theorem node_at (i : ℕ) (hi : i<640) : tape.node i=GridPlus.atNode i := (range i hi).1
end
end SolitonClassification.Rotating.DyadicReset.HullPlus
