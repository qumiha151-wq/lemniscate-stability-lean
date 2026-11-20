import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [96,96,96,96,96,96,96,96,96,96,96,96,96,96,96,96]
  344088830457769460935874513831842481352766615997306461585333362097567314147705377511686786335803645471844933833067737008783760002917157662431424150732300 79202268779223877811627685903301436228612485990162193869835654777358462930669155338392405084103474676733926687953296467412563806364046846803371907861036 30074313255393391625922976202308026280149777487212684721202095384621038167607297172169670945369728045301474753733578507419836302213700391361593685833754 100338346706550067141299686355243157994098964414384437635959777494140946693734805802062663034068825764998118346728700049110163328988752700979657043189109

private def left : Mark := ⟨172044415228884730467937256915921240676383307998653230792666681048783657073852688755843393167901822735922466916533868504391880001458578831215712075366150,39601134389611938905813842951650718114306242995081096934917827388679231465334577669196202542051737338366963343976648233706281903182023423401685953930518,15037156627696695812961488101154013140074888743606342360601047692310519083803648586084835472684864022650737376866789253709918151106850195680796842916877,(-50169173353275033570649843177621578997049482207192218817979888747070473346867402901031331517034412882499059173364350024555081664494376350489828521594555)⟩
private def right : Mark := ⟨91404908929698793653761517899906681516027207330988723304415954866111519615341446538112519660261495154906022458604595367059628810863378945126556895902890,(-287918917128777551000017558673562934046695345549194538164249014705737902302114635214379943531774278059470783617742234388091343485836532905743041723102160),52048021667008168864856742618569804656902781458300794911408781725891458460992635332841356078830188157326490556244920525739752869295528387417068229449156,5836563624898861344447415366852750130457239349591076883060924541291962557914337999857081165739909117163685597239675091053685793040805041877129050849894⟩

private theorem cell0 : Transports 272 273 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 272 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 273 274 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 273 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 274 275 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 274 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 275 276 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 275 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 276 277 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 276 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 277 278 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 277 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 278 279 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 278 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 279 280 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 279 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 280 281 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 280 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 281 282 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 281 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 282 283 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 282 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 283 284 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 283 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 284 285 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 284 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 285 286 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 285 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 286 287 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 286 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 287 288 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 287 _ _ (by decide) (by decide +kernel)

theorem positive_transport_272_288 : Transports 272 288 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_272_288
