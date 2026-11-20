import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [96,96,96,96,96,96,92,92,92,92,92,92,92,92,92,92]
  246611094300717504912181720556332756890438458377042650131720465328698638425535865245411668123814499241310239453044704007431319850841824097945459777255671 628004680811644633666836185823495554025373374400913783140933074780812060908044713805074463401507351189402456705069713558798284407484126370335532675224962 96960874246642471104903436287198756771565303578626722124161030680683263652396424818984065972038803472715594138125560751568089760726412705529148854365469 39633786128935022273077296287845685803580895263087001674094376295572078351926766357315937482250954052331484791983784823139403588491438808475491924678147

private def left : Mark := ⟨(-123305547150358752456090860278166378445219229188521325065860232664349319212767932622705834061907249620655119726522352003715659925420912048972729888627836),314002340405822316833418092911747777012686687200456891570466537390406030454022356902537231700753675594701228352534856779399142203742063185167766337612481,(-48480437123321235552451718143599378385782651789313361062080515340341631826198212409492032986019401736357797069062780375784044880363206352764574427182735),(-19816893064467511136538648143922842901790447631543500837047188147786039175963383178657968741125477026165742395991892411569701794245719404237745962339074)⟩
private def right : Mark := ⟨53608147146255402943857140735136337611780050664849095608123399359486756255525310027317098423803486994057264212641591057275080673754998111731725753040258,370509389296306628430585421942296822057482471872410274526726349289769148064745936021616378110203295090262039543398422341942701722017154852253641063002776,(-52338789230385732370184559749780645583043960878585201637339609856518542317503490244325257033457145909848781716847994921777808152191042656593649599497851),(-1926960376889680179513921520863441295441305863085320229261591926369340232684172698358476469646025589240072869326194071087088168660939622289495318149553)⟩

private theorem cell0 : Transports 320 321 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 320 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 321 322 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 321 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 322 323 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 322 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 323 324 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 323 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 324 325 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 324 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 325 326 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 325 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 326 327 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 326 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 327 328 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 327 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 328 329 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 328 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 329 330 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 329 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 330 331 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 330 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 331 332 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 331 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 332 333 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 332 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 333 334 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 333 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 334 335 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 334 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 335 336 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 335 _ _ (by decide) (by decide +kernel)

theorem negative_transport_320_336 : Transports 320 336 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_320_336
