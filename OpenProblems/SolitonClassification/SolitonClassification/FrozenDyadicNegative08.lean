import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [88,88,88,88,88,88,88,88,88,88,88,88,88,88,88,88]
  167490090902310993674165578146346523429039945341218599480559600452019856170362101505581246219920907649669695987359707180741439699767616552100012738228542 271498908966592415118656084119108487558502626588937752430794627344782358883523291599319615967744810675731899826482644749069161296115431946541834579129768 95610028061396075509785458144865223352078233842255429683754359320155726215619789842076762219499170468937808483413950731983879314697463215119525694940209 42789843090229162063526254036948340480545062515163329807873393823218135528195212946764458224443217824184935869965400004739336027508983442361186119212933

private def left : Mark := ⟨83745045451155496837082789073173261714519972670609299740279800226009928085181050752790623109960453824834847993679853590370719849883808276050006369114271,135749454483296207559328042059554243779251313294468876215397313672391179441761645799659807983872405337865949913241322374534580648057715973270917289564884,(-47805014030698037754892729072432611676039116921127714841877179660077863107809894921038381109749585234468904241706975365991939657348731607559762847470105),(-21394921545114581031763127018474170240272531257581664903936696911609067764097606473382229112221608912092467934982700002369668013754491721180593059606467)⟩
private def right : Mark := ⟨129738676405068805066956507093531777330882925769072048258191104255688385545080606506135939577123917256350618476165309470099649345353049956870564171138598,18232903665734769516709965447238097683026283288395894944612671244432451578260399848011846020551745619135623526885647341937114794659886206733101217698808,(-4389534588526684852100329098568215596156397392024601405030345599186561791805019765377305502941647037577307199637945795718690825980545836209359734266322),(-52189980077529941601072262970265566985239045252957942241558499920241408956123102881552528167443676128595627036706095471898337159996319415382134431684946)⟩

private theorem cell0 : Transports 128 129 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 128 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 129 130 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 129 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 130 131 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 130 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 131 132 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 131 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 132 133 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 132 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 133 134 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 133 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 134 135 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 134 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 135 136 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 135 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 136 137 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 136 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 137 138 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 137 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 138 139 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 138 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 139 140 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 139 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 140 141 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 140 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 141 142 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 141 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 142 143 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 142 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 143 144 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 143 _ _ (by decide) (by decide +kernel)

theorem negative_transport_128_144 : Transports 128 144 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_128_144
