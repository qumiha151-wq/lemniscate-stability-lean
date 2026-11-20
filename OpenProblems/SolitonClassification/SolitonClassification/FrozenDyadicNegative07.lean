import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [80,80,80,84,84,84,84,84,84,84,84,84,84,84,84,88]
  32143247901928337839355950618652791674224984280409696341624410360996953397805315573730158107643400711350827204661381136272889582735948775768914641154520 252550129920957981412809641698041117540806507831955881579120706379999438676824651627273763414113753042280312919521533520848456684412506395423800485682720 104612483583867414612217303590599883687265483106185144621936405335074381586854599739471511423653272955312029538968012547555382366520545695427384041204137 5336329825118388881316206137745296837140266573863936357112280608955996982129663528870999338058593464516072404684985370645189914280721156237304611148974

private def left : Mark := ⟨16071623950964168919677975309326395837112492140204848170812205180498476698902657786865079053821700355675413602330690568136444791367974387884457320577260,126275064960478990706404820849020558770403253915977940789560353189999719338412325813636881707056876521140156459760766760424228342206253197711900242841360,(-52306241791933707306108651795299941843632741553092572310968202667537190793427299869735755711826636477656014769484006273777691183260272847713692020602069),2668164912559194440658103068872648418570133286931968178556140304477998491064831764435499669029296732258036202342492685322594957140360578118652305574487⟩
private def right : Mark := ⟨83745045451155496837082789073173261714519972670609299740279800226009928085181050752790623109960453824834847993679853590370719849883808276050006369114271,135749454483296207559328042059554243779251313294468876215397313672391179441761645799659807983872405337865949913241322374534580648057715973270917289564884,(-47805014030698037754892729072432611676039116921127714841877179660077863107809894921038381109749585234468904241706975365991939657348731607559762847470105),(-21394921545114581031763127018474170240272531257581664903936696911609067764097606473382229112221608912092467934982700002369668013754491721180593059606467)⟩

private theorem cell0 : Transports 112 113 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 112 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 113 114 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 113 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 114 115 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 114 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 115 116 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 115 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 116 117 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 116 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 117 118 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 117 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 118 119 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 118 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 119 120 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 119 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 120 121 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 120 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 121 122 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 121 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 122 123 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 122 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 123 124 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 123 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 124 125 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 124 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 125 126 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 125 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 126 127 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 126 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 127 128 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 127 _ _ (by decide) (by decide +kernel)

theorem negative_transport_112_128 : Transports 112 128 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_112_128
