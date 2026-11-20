import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [96,96,92,92,92,92,92,92,92,92,88,88,88,88,92,92]
  234549633668594682059646717477866163401282700742013073648350935315426146286290996311006740015086745308568142647718167004384258726122938175504101224051392 524496554285538984212204219199019248097567843737507585407747252572601920599482275294740204644917348699182346937408763304068903327977664464193735226596399 92233211669079249947007828245632942838047793222007354117617706921627723236548585865933819042843470231555926107840129661498914710806016944458413242983724 49651614301996271012205750300320291322099884557665953010511382196917838344257843202010256999188689494408031256230422847802775076880952453489876799774867

private def left : Mark := ⟨117274816834297341029823358738933081700641350371006536824175467657713073143145498155503370007543372654284071323859083502192129363061469087752050612025696,(-262248277142769492106102109599509624048783921868753792703873626286300960299741137647370102322458674349591173468704381652034451663988832232096867613298200),46116605834539624973503914122816471419023896611003677058808853460813861618274292932966909521421735115777963053920064830749457355403008472229206621491862,(-24825807150998135506102875150160145661049942278832976505255691098458919172128921601005128499594344747204015628115211423901387538440476226744938399887434)⟩
private def right : Mark := ⟨(-32972239544616534996519343365025390093506219042224264132365818485208363206572517031411777957693164709607421087081587530608812002732427829188512602581914),(-318308323115202197779490319981722200913248081851321090066894103878421280822410490222367791865586246813719693905175204049939703897212688752375481450437082),52236705705697572307395267591925976383053374117255845852791319379669751433948075620189049626690965163626993374623904930070745248126585025170930534041470,(-3793232317323450720860253796368298549300367544909457527110875304901134354876503704151896836417038481421527992467347973747071520909349923787474370422176)⟩

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

theorem negative_transport_272_288 : Transports 272 288 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_272_288
