import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [96,96,96,96,96,96,100,100,100,100,100,100,100,100,100,104]
  107216294292510805887714281470272675223560101329698191216246798718973512511050620054634196847606973988114528425283182114550161347509996223463451506080516 741018778592613256861170843884593644114964943744820549053452698579538296129491872043232756220406590180524079086796844683885403444034309704507282126005552 104677578460771464740369119499561291166087921757170403274679219713037084635006980488650514066914291819697563433695989843555616304382085313187299198995701 3853920753779360359027843041726882590882611726170640458523183852738680465368345396716952939292051178480145738652388142174176337321879244578990636299105

private def left : Mark := ⟨53608147146255402943857140735136337611780050664849095608123399359486756255525310027317098423803486994057264212641591057275080673754998111731725753040258,370509389296306628430585421942296822057482471872410274526726349289769148064745936021616378110203295090262039543398422341942701722017154852253641063002776,(-52338789230385732370184559749780645583043960878585201637339609856518542317503490244325257033457145909848781716847994921777808152191042656593649599497851),(-1926960376889680179513921520863441295441305863085320229261591926369340232684172698358476469646025589240072869326194071087088168660939622289495318149553)⟩
private def right : Mark := ⟨199711707420421377918728125087773615619885911406475451773134903319127983586379920963848156254659857179977523414213545644742629140451554474638274052467194,77487992341248857200005016465742619053607894221135870302504034877006421927291987767608278750395289501975723855548367237050186258275659918108403417067749,(-11143023612543693627382913226378881258386715123878488440352303087225130028993364870947431221782404495826508577736232217203043153472590773222492006775082),(-51175141027330232783154299810898145548012659108990482275439702799636229147520991015155013117258544470449558560694617493675518838727349709144610629993906)⟩

private theorem cell0 : Transports 336 337 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 336 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 337 338 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 337 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 338 339 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 338 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 339 340 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 339 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 340 341 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 340 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 341 342 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 341 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 342 343 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 342 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 343 344 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 343 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 344 345 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 344 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 345 346 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 345 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 346 347 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 346 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 347 348 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 347 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 348 349 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 348 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 349 350 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 349 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 350 351 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 350 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 351 352 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 351 _ _ (by decide) (by decide +kernel)

theorem negative_transport_336_352 : Transports 336 352 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_336_352
