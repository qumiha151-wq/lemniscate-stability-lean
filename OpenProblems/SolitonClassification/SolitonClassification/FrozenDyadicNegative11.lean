import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [84,84,84,84,84,88,88,88,88,88,88,88,88,88,88,92]
  7947713732875617113222260549659220372320886372887272644076136167311193415043598752806553470896855643465838834803803169715957182967302202949802502496604 388200635960761241625062979420451472043470823651929009847495542450422246962550674673206499314916751796360086065864144565114551759430983829861628846504835 104619264294294875387036587664434621025366667011435885460225268856304171263963332210482973513088246167460596452418891982245600065777034865742405850314444 5201699348083735219314517624328997468408810133004997784545333536812461873644314105041575716511219759937830966830849044609745339320734863448896769581059

private def left : Mark := ⟨3973856866437808556611130274829610186160443186443636322038068083655596707521799376403276735448427821732919417401901584857978591483651101474901251248302,(-194100317980380620812531489710225736021735411825964504923747771225211123481275337336603249657458375898180043032932072282557275879715491914930814423252418),52309632147147437693518293832217310512683333505717942730112634428152085631981666105241486756544123083730298226209445991122800032888517432871202925157222,(-2600849674041867609657258812164498734204405066502498892272666768406230936822157052520787858255609879968915483415424522304872669660367431724448384790530)⟩
private def right : Mark := ⟨(-97637618251361182479629725343360777515047826047245343393314405865658147148372690788876021165256901397811678271941323747204225795329575351655484638832792),(-199377194175007027142262913271170689155714122135830992631159387806614724081654948611261367276339425368085288264096716233918124942389511439127503861005283),46141834433024560714289280985324845900178561496936704327722996173843936286702716361154566958572567996599149677119535333910114841387225550824994166795867,(-24778885155555190096668310849567182283216797958791948603455828179382306826261614534628971290117299785066323001404891659152888288587556579598225180808098)⟩

private theorem cell0 : Transports 176 177 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 176 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 177 178 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 177 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 178 179 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 178 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 179 180 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 179 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 180 181 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 180 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 181 182 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 181 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 182 183 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 182 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 183 184 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 183 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 184 185 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 184 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 185 186 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 185 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 186 187 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 186 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 187 188 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 187 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 188 189 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 188 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 189 190 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 189 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 190 191 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 190 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 191 192 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 191 _ _ (by decide) (by decide +kernel)

theorem negative_transport_176_192 : Transports 176 192 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_176_192
