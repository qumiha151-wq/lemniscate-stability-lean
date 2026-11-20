import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [92,92,92,92,92,96,96,96,96,96,96,96,96,96,96,96]
  145995096306351646428211354937368626837204229805066340280861833975647028060363088333741185218864330249239720623055483491757289441665637321038499677076538 542810594511283632315848113638907097411940066828935079055997594231193566118401228353490624714464814011086283400435785435544732498379940144534673249640524 86367652420189742019458451910227545699256990175945275743034039053966372147557980265899420093659442803012112379047810748716741839139008308801462784609113 59269526343751646051417126525139370902187633637072599773404697725655890077605824119494745455953587127587917268844238518442076265574621985610456474706313

private def left : Mark := ⟨72997548153175823214105677468684313418602114902533170140430916987823514030181544166870592609432165124619860311527741745878644720832818660519249838538269,271405297255641816157924056819453548705970033414467539527998797115596783059200614176745312357232407005543141700217892717772366249189970072267336624820262,(-43183826210094871009729225955113772849628495087972637871517019526983186073778990132949710046829721401506056189523905374358370919569504154400731392304557),(-29634763171875823025708563262569685451093816818536299886702348862827945038802912059747372727976793563793958634422119259221038132787310992805228237353157)⟩
private def right : Mark := ⟨172044415228884730467937256915921240676383307998653230792666681048783657073852688755843393167901822735922466916533868504391880001458578831215712075366150,39601134389611938905813842951650718114306242995081096934917827388679231465334577669196202542051737338366963343976648233706281903182023423401685953930518,15037156627696695812961488101154013140074888743606342360601047692310519083803648586084835472684864022650737376866789253709918151106850195680796842916877,(-50169173353275033570649843177621578997049482207192218817979888747070473346867402901031331517034412882499059173364350024555081664494376350489828521594555)⟩

private theorem cell0 : Transports 256 257 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 256 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 257 258 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 257 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 258 259 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 258 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 259 260 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 259 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 260 261 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 260 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 261 262 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 261 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 262 263 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 262 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 263 264 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 263 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 264 265 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 264 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 265 266 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 265 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 266 267 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 266 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 267 268 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 267 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 268 269 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 268 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 269 270 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 269 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 270 271 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 270 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 271 272 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 271 _ _ (by decide) (by decide +kernel)

theorem positive_transport_256_272 : Transports 256 272 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_256_272
