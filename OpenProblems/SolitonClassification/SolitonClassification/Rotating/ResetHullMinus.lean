import SolitonClassification.Rotating.ResetTileMinus00
import SolitonClassification.Rotating.ResetTileMinus01
import SolitonClassification.Rotating.ResetTileMinus02
import SolitonClassification.Rotating.ResetTileMinus03
import SolitonClassification.Rotating.ResetTileMinus04
import SolitonClassification.Rotating.ResetTileMinus05
import SolitonClassification.Rotating.ResetTileMinus06
import SolitonClassification.Rotating.ResetTileMinus07
import SolitonClassification.Rotating.ResetTileMinus08
import SolitonClassification.Rotating.ResetTileMinus09
import SolitonClassification.Rotating.ResetTileMinus10
import SolitonClassification.Rotating.ResetTileMinus11
import SolitonClassification.Rotating.ResetTileMinus12
import SolitonClassification.Rotating.ResetTileMinus13
import SolitonClassification.Rotating.ResetTileMinus14
import SolitonClassification.Rotating.ResetTileMinus15
import SolitonClassification.Rotating.ResetTileMinus16
import SolitonClassification.Rotating.ResetTileMinus17
import SolitonClassification.Rotating.ResetTileMinus18
import SolitonClassification.Rotating.ResetTileMinus19
import SolitonClassification.Rotating.ResetTileMinus20
import SolitonClassification.Rotating.ResetTileMinus21
import SolitonClassification.Rotating.ResetTileMinus22
import SolitonClassification.Rotating.ResetTileMinus23
import SolitonClassification.Rotating.ResetTileMinus24
import SolitonClassification.Rotating.ResetTileMinus25
import SolitonClassification.Rotating.ResetTileMinus26
import SolitonClassification.Rotating.ResetTileMinus27
import SolitonClassification.Rotating.ResetTileMinus28
import SolitonClassification.Rotating.ResetTileMinus29
import SolitonClassification.Rotating.ResetTileMinus30
import SolitonClassification.Rotating.ResetTileMinus31
import SolitonClassification.Rotating.ResetTileMinus32
import SolitonClassification.Rotating.ResetTileMinus33
import SolitonClassification.Rotating.ResetTileMinus34
import SolitonClassification.Rotating.ResetTileMinus35
import SolitonClassification.Rotating.ResetTileMinus36
import SolitonClassification.Rotating.ResetTileMinus37
import SolitonClassification.Rotating.ResetTileMinus38
import SolitonClassification.Rotating.ResetTileMinus39
import SolitonClassification.Rotating.ResetTileMinus40
import SolitonClassification.Rotating.ResetTileMinus41
import SolitonClassification.Rotating.ResetTileMinus42
import SolitonClassification.Rotating.ResetTileMinus43
import SolitonClassification.Rotating.ResetTileMinus44
import SolitonClassification.Rotating.ResetTileMinus45
import SolitonClassification.Rotating.ResetTileMinus46
import SolitonClassification.Rotating.ResetTileMinus47
import SolitonClassification.Rotating.ResetTileMinus48
import SolitonClassification.Rotating.ResetTileMinus49
namespace SolitonClassification.Rotating.DyadicReset.HullMinus
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def cellBlock : ℕ→ℕ→TapeRow (-Middle.hn)
  | 0 => TileMinus00.atRow
  | 1 => TileMinus01.atRow
  | 2 => TileMinus02.atRow
  | 3 => TileMinus03.atRow
  | 4 => TileMinus04.atRow
  | 5 => TileMinus05.atRow
  | 6 => TileMinus06.atRow
  | 7 => TileMinus07.atRow
  | 8 => TileMinus08.atRow
  | 9 => TileMinus09.atRow
  | 10 => TileMinus10.atRow
  | 11 => TileMinus11.atRow
  | 12 => TileMinus12.atRow
  | 13 => TileMinus13.atRow
  | 14 => TileMinus14.atRow
  | 15 => TileMinus15.atRow
  | 16 => TileMinus16.atRow
  | 17 => TileMinus17.atRow
  | 18 => TileMinus18.atRow
  | 19 => TileMinus19.atRow
  | 20 => TileMinus20.atRow
  | 21 => TileMinus21.atRow
  | 22 => TileMinus22.atRow
  | 23 => TileMinus23.atRow
  | 24 => TileMinus24.atRow
  | 25 => TileMinus25.atRow
  | 26 => TileMinus26.atRow
  | 27 => TileMinus27.atRow
  | 28 => TileMinus28.atRow
  | 29 => TileMinus29.atRow
  | 30 => TileMinus30.atRow
  | 31 => TileMinus31.atRow
  | 32 => TileMinus32.atRow
  | 33 => TileMinus33.atRow
  | 34 => TileMinus34.atRow
  | 35 => TileMinus35.atRow
  | 36 => TileMinus36.atRow
  | 37 => TileMinus37.atRow
  | 38 => TileMinus38.atRow
  | 39 => TileMinus39.atRow
  | 40 => TileMinus40.atRow
  | 41 => TileMinus41.atRow
  | 42 => TileMinus42.atRow
  | 43 => TileMinus43.atRow
  | 44 => TileMinus44.atRow
  | 45 => TileMinus45.atRow
  | 46 => TileMinus46.atRow
  | 47 => TileMinus47.atRow
  | 48 => TileMinus48.atRow
  | 49 => TileMinus49.atRow
  | _ => TileMinus00.atRow
theorem indexes (b j : ℕ) (hb : b<50) (hj : j<64) :
    (cellBlock b j).left=GridMinus.atNode (64*b+j) ∧ (cellBlock b j).right=GridMinus.atNode (64*b+j+1) := by
  interval_cases b
  · exact TileMinus00.at_index j hj
  · exact TileMinus01.at_index j hj
  · exact TileMinus02.at_index j hj
  · exact TileMinus03.at_index j hj
  · exact TileMinus04.at_index j hj
  · exact TileMinus05.at_index j hj
  · exact TileMinus06.at_index j hj
  · exact TileMinus07.at_index j hj
  · exact TileMinus08.at_index j hj
  · exact TileMinus09.at_index j hj
  · exact TileMinus10.at_index j hj
  · exact TileMinus11.at_index j hj
  · exact TileMinus12.at_index j hj
  · exact TileMinus13.at_index j hj
  · exact TileMinus14.at_index j hj
  · exact TileMinus15.at_index j hj
  · exact TileMinus16.at_index j hj
  · exact TileMinus17.at_index j hj
  · exact TileMinus18.at_index j hj
  · exact TileMinus19.at_index j hj
  · exact TileMinus20.at_index j hj
  · exact TileMinus21.at_index j hj
  · exact TileMinus22.at_index j hj
  · exact TileMinus23.at_index j hj
  · exact TileMinus24.at_index j hj
  · exact TileMinus25.at_index j hj
  · exact TileMinus26.at_index j hj
  · exact TileMinus27.at_index j hj
  · exact TileMinus28.at_index j hj
  · exact TileMinus29.at_index j hj
  · exact TileMinus30.at_index j hj
  · exact TileMinus31.at_index j hj
  · exact TileMinus32.at_index j hj
  · exact TileMinus33.at_index j hj
  · exact TileMinus34.at_index j hj
  · exact TileMinus35.at_index j hj
  · exact TileMinus36.at_index j hj
  · exact TileMinus37.at_index j hj
  · exact TileMinus38.at_index j hj
  · exact TileMinus39.at_index j hj
  · exact TileMinus40.at_index j hj
  · exact TileMinus41.at_index j hj
  · exact TileMinus42.at_index j hj
  · exact TileMinus43.at_index j hj
  · exact TileMinus44.at_index j hj
  · exact TileMinus45.at_index j hj
  · exact TileMinus46.at_index j hj
  · exact TileMinus47.at_index j hj
  · exact TileMinus48.at_index j hj
  · exact TileMinus49.at_index j hj
def atRow (i : ℕ) := cellBlock (i/64) (i%64)
theorem range (i : ℕ) (hi : i<3200) : (atRow i).left=GridMinus.atNode i ∧ (atRow i).right=GridMinus.atNode (i+1) := by
  have eq : 64*(i/64)+i%64=i := Nat.div_add_mod i 64
  have b := indexes (i/64) (i%64) (by omega) (Nat.mod_lt _ (by decide))
  simpa only [atRow,eq] using b
theorem links (i : ℕ) (hi : i+1<3200) : (atRow i).right=(atRow (i+1)).left :=
  (range i (by omega)).2.trans (range (i+1) hi).1.symm
def tape : PolynomialTape (-Middle.hn) 3200 := assemble atRow links
theorem node_at (i : ℕ) (hi : i<3200) : tape.node i=GridMinus.atNode i := (range i hi).1
end
end SolitonClassification.Rotating.DyadicReset.HullMinus
