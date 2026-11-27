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
import SolitonClassification.Rotating.ResetTilePlus10
import SolitonClassification.Rotating.ResetTilePlus11
import SolitonClassification.Rotating.ResetTilePlus12
import SolitonClassification.Rotating.ResetTilePlus13
import SolitonClassification.Rotating.ResetTilePlus14
import SolitonClassification.Rotating.ResetTilePlus15
import SolitonClassification.Rotating.ResetTilePlus16
import SolitonClassification.Rotating.ResetTilePlus17
import SolitonClassification.Rotating.ResetTilePlus18
import SolitonClassification.Rotating.ResetTilePlus19
import SolitonClassification.Rotating.ResetTilePlus20
import SolitonClassification.Rotating.ResetTilePlus21
import SolitonClassification.Rotating.ResetTilePlus22
import SolitonClassification.Rotating.ResetTilePlus23
import SolitonClassification.Rotating.ResetTilePlus24
import SolitonClassification.Rotating.ResetTilePlus25
import SolitonClassification.Rotating.ResetTilePlus26
import SolitonClassification.Rotating.ResetTilePlus27
import SolitonClassification.Rotating.ResetTilePlus28
import SolitonClassification.Rotating.ResetTilePlus29
import SolitonClassification.Rotating.ResetTilePlus30
import SolitonClassification.Rotating.ResetTilePlus31
import SolitonClassification.Rotating.ResetTilePlus32
import SolitonClassification.Rotating.ResetTilePlus33
import SolitonClassification.Rotating.ResetTilePlus34
import SolitonClassification.Rotating.ResetTilePlus35
import SolitonClassification.Rotating.ResetTilePlus36
import SolitonClassification.Rotating.ResetTilePlus37
import SolitonClassification.Rotating.ResetTilePlus38
import SolitonClassification.Rotating.ResetTilePlus39
import SolitonClassification.Rotating.ResetTilePlus40
import SolitonClassification.Rotating.ResetTilePlus41
import SolitonClassification.Rotating.ResetTilePlus42
import SolitonClassification.Rotating.ResetTilePlus43
import SolitonClassification.Rotating.ResetTilePlus44
import SolitonClassification.Rotating.ResetTilePlus45
import SolitonClassification.Rotating.ResetTilePlus46
import SolitonClassification.Rotating.ResetTilePlus47
import SolitonClassification.Rotating.ResetTilePlus48
import SolitonClassification.Rotating.ResetTilePlus49
import SolitonClassification.Rotating.ResetTilePlus50
import SolitonClassification.Rotating.ResetTilePlus51
import SolitonClassification.Rotating.ResetTilePlus52
import SolitonClassification.Rotating.ResetTilePlus53
import SolitonClassification.Rotating.ResetTilePlus54
import SolitonClassification.Rotating.ResetTilePlus55
import SolitonClassification.Rotating.ResetTilePlus56
import SolitonClassification.Rotating.ResetTilePlus57
import SolitonClassification.Rotating.ResetTilePlus58
import SolitonClassification.Rotating.ResetTilePlus59
import SolitonClassification.Rotating.ResetTilePlus60
import SolitonClassification.Rotating.ResetTilePlus61
import SolitonClassification.Rotating.ResetTilePlus62
namespace SolitonClassification.Rotating.DyadicReset.CompletePlus
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def cellBlock : ℕ→ℕ→TapeRow Middle.hn
  | 0=>TilePlus00.atRow
  | 1=>TilePlus01.atRow
  | 2=>TilePlus02.atRow
  | 3=>TilePlus03.atRow
  | 4=>TilePlus04.atRow
  | 5=>TilePlus05.atRow
  | 6=>TilePlus06.atRow
  | 7=>TilePlus07.atRow
  | 8=>TilePlus08.atRow
  | 9=>TilePlus09.atRow
  | 10=>TilePlus10.atRow
  | 11=>TilePlus11.atRow
  | 12=>TilePlus12.atRow
  | 13=>TilePlus13.atRow
  | 14=>TilePlus14.atRow
  | 15=>TilePlus15.atRow
  | 16=>TilePlus16.atRow
  | 17=>TilePlus17.atRow
  | 18=>TilePlus18.atRow
  | 19=>TilePlus19.atRow
  | 20=>TilePlus20.atRow
  | 21=>TilePlus21.atRow
  | 22=>TilePlus22.atRow
  | 23=>TilePlus23.atRow
  | 24=>TilePlus24.atRow
  | 25=>TilePlus25.atRow
  | 26=>TilePlus26.atRow
  | 27=>TilePlus27.atRow
  | 28=>TilePlus28.atRow
  | 29=>TilePlus29.atRow
  | 30=>TilePlus30.atRow
  | 31=>TilePlus31.atRow
  | 32=>TilePlus32.atRow
  | 33=>TilePlus33.atRow
  | 34=>TilePlus34.atRow
  | 35=>TilePlus35.atRow
  | 36=>TilePlus36.atRow
  | 37=>TilePlus37.atRow
  | 38=>TilePlus38.atRow
  | 39=>TilePlus39.atRow
  | 40=>TilePlus40.atRow
  | 41=>TilePlus41.atRow
  | 42=>TilePlus42.atRow
  | 43=>TilePlus43.atRow
  | 44=>TilePlus44.atRow
  | 45=>TilePlus45.atRow
  | 46=>TilePlus46.atRow
  | 47=>TilePlus47.atRow
  | 48=>TilePlus48.atRow
  | 49=>TilePlus49.atRow
  | 50=>TilePlus50.atRow
  | 51=>TilePlus51.atRow
  | 52=>TilePlus52.atRow
  | 53=>TilePlus53.atRow
  | 54=>TilePlus54.atRow
  | 55=>TilePlus55.atRow
  | 56=>TilePlus56.atRow
  | 57=>TilePlus57.atRow
  | 58=>TilePlus58.atRow
  | 59=>TilePlus59.atRow
  | 60=>TilePlus60.atRow
  | 61=>TilePlus61.atRow
  | 62=>TilePlus62.atRow
  | _=>TilePlus00.atRow
theorem indexes (b j : ℕ) (hb : b<63) (hj : j<64) (total : 64*b+j<4000) :
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
  · exact TilePlus10.at_index j hj
  · exact TilePlus11.at_index j hj
  · exact TilePlus12.at_index j hj
  · exact TilePlus13.at_index j hj
  · exact TilePlus14.at_index j hj
  · exact TilePlus15.at_index j hj
  · exact TilePlus16.at_index j hj
  · exact TilePlus17.at_index j hj
  · exact TilePlus18.at_index j hj
  · exact TilePlus19.at_index j hj
  · exact TilePlus20.at_index j hj
  · exact TilePlus21.at_index j hj
  · exact TilePlus22.at_index j hj
  · exact TilePlus23.at_index j hj
  · exact TilePlus24.at_index j hj
  · exact TilePlus25.at_index j hj
  · exact TilePlus26.at_index j hj
  · exact TilePlus27.at_index j hj
  · exact TilePlus28.at_index j hj
  · exact TilePlus29.at_index j hj
  · exact TilePlus30.at_index j hj
  · exact TilePlus31.at_index j hj
  · exact TilePlus32.at_index j hj
  · exact TilePlus33.at_index j hj
  · exact TilePlus34.at_index j hj
  · exact TilePlus35.at_index j hj
  · exact TilePlus36.at_index j hj
  · exact TilePlus37.at_index j hj
  · exact TilePlus38.at_index j hj
  · exact TilePlus39.at_index j hj
  · exact TilePlus40.at_index j hj
  · exact TilePlus41.at_index j hj
  · exact TilePlus42.at_index j hj
  · exact TilePlus43.at_index j hj
  · exact TilePlus44.at_index j hj
  · exact TilePlus45.at_index j hj
  · exact TilePlus46.at_index j hj
  · exact TilePlus47.at_index j hj
  · exact TilePlus48.at_index j hj
  · exact TilePlus49.at_index j hj
  · exact TilePlus50.at_index j hj
  · exact TilePlus51.at_index j hj
  · exact TilePlus52.at_index j hj
  · exact TilePlus53.at_index j hj
  · exact TilePlus54.at_index j hj
  · exact TilePlus55.at_index j hj
  · exact TilePlus56.at_index j hj
  · exact TilePlus57.at_index j hj
  · exact TilePlus58.at_index j hj
  · exact TilePlus59.at_index j hj
  · exact TilePlus60.at_index j hj
  · exact TilePlus61.at_index j hj
  · exact TilePlus62.at_index j (by omega)
def atRow (i : ℕ) := cellBlock (i/64) (i%64)
theorem range (i : ℕ) (hi : i<4000) : (atRow i).left=GridPlus.atNode i ∧ (atRow i).right=GridPlus.atNode (i+1) := by
  have sub : i%64<64 := Nat.mod_lt _ (by decide)
  have eq : 64*(i/64)+i%64=i := Nat.div_add_mod i 64
  have b:=indexes (i/64) (i%64) (by omega) sub (by omega)
  simpa only [atRow,eq] using b
theorem links (i : ℕ) (hi : i+1<4000) : (atRow i).right=(atRow (i+1)).left :=
  (range i (by omega)).2.trans (range (i+1) hi).1.symm
def tape : PolynomialTape Middle.hn 4000 := assemble atRow links
end
end SolitonClassification.Rotating.DyadicReset.CompletePlus
