import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [92,92,92,92,92,96,96,96,96,96,96,96,100,100,100,100]
  65944479089233069993038686730050780187012438084448528264731636970416726413145034062823555915386329419214842174163175061217624005464855658377025205163827 636616646230404395558980639963444401826496163702642180133788207756842561644820980444735583731172493627439387810350408099879407794425377504750962900874163 104473411411395144614790535183851952766106748234511691705582638759339502867896151240378099253381930327253986749247809860141490496253170050341861068082940 7586464634646901441720507592736597098600735089818915054221750609802268709753007408303793672834076962843055984934695947494143041818699847574948740844351

private def left : Mark := ⟨(-32972239544616534996519343365025390093506219042224264132365818485208363206572517031411777957693164709607421087081587530608812002732427829188512602581914),(-318308323115202197779490319981722200913248081851321090066894103878421280822410490222367791865586246813719693905175204049939703897212688752375481450437082),52236705705697572307395267591925976383053374117255845852791319379669751433948075620189049626690965163626993374623904930070745248126585025170930534041470,(-3793232317323450720860253796368298549300367544909457527110875304901134354876503704151896836417038481421527992467347973747071520909349923787474370422176)⟩
private def right : Mark := ⟨(-175812993135793250357416102834922767733423377234618055601666071365146374775362648284371998980255530905386116613808117683231636281401708596305603084579205),(-165444520338179967400542274685878967806502529450307739475304340007054497091799873917203610307203683402557396434500349190595601350689229801339710791220815),22676650371769267449921553417489235327957093568394042984722649724689844361990358790819346695526723243918965661031238245397919960097254791765824544615341,(-47210502669568993755419242503376008273444558751986807302294895377983047476997067550084002968192650905339083871663375500297360101541580298550263290582330)⟩

private theorem cell0 : Transports 288 289 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 288 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 289 290 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 289 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 290 291 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 290 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 291 292 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 291 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 292 293 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 292 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 293 294 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 293 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 294 295 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 294 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 295 296 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 295 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 296 297 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 296 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 297 298 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 297 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 298 299 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 298 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 299 300 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 299 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 300 301 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 300 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 301 302 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 301 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 302 303 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 302 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 303 304 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 303 _ _ (by decide) (by decide +kernel)

theorem negative_transport_288_304 : Transports 288 304 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_288_304
