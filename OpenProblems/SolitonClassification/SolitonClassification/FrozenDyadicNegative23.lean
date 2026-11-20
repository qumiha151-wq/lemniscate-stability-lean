import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [96,96,96,96,96,92,92,92,92,96,96,96,96,96,96,100]
  176156412305489307081639799215252926179814587369273627666621328149623576835795310033764724757430857133801816076119094100677035862784268552413633880050820 786624857307708799244875432432203249508933671734020530090374415041771968378592432223420072763674302122382460840854234996045483639510858519120736087757573 102241025640548138438359814988896071903503948360726374467797445874839762518852444705273793344355562984797148957102204681083719140973007419188606118500144 22782028302066422563571109618119823012397119756149756251230144016573022886723812611165245036160823562240461534252111653526722401335644437238389474751399

private def left : Mark := ⟨88078206152744653540819899607626463089907293684636813833310664074811788417897655016882362378715428566900908038059547050338517931392134276206816940025410,(-393312428653854399622437716216101624754466835867010265045187207520885984189296216111710036381837151061191230420427117498022741819755429259560368043878787),51120512820274069219179907494448035951751974180363187233898722937419881259426222352636896672177781492398574478551102340541859570486503709594303059250072,(-11391014151033211281785554809059911506198559878074878125615072008286511443361906305582622518080411781120230767126055826763361200667822218619194737375700)⟩
private def right : Mark := ⟨(-117047298871766388989322152333997581477523848695174206921142455280306090241664608232837074851853126854733935891179775531138059315995438407106127808456806),(-405378286605349103769462685853084833168767747618085363391165071510069053371501038243890478939432280496400376475977128458278943372428932775505590344562992),49190534904683581263399845664309159527868364479418266157380406024560087243807636208706162053849364529521938464613878221332976999119455100303146821430493,(-17982027421510361950477956653890370128986945565171723862539165439732955346043107210588233645209331774399240712581472333320540444205957145006323546910596)⟩

private theorem cell0 : Transports 368 369 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 368 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 369 370 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 369 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 370 371 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 370 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 371 372 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 371 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 372 373 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 372 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 373 374 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 373 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 374 375 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 374 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 375 376 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 375 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 376 377 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 376 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 377 378 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 377 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 378 379 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 378 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 379 380 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 379 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 380 381 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 380 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 381 382 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 381 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 382 383 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 382 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 383 384 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 383 _ _ (by decide) (by decide +kernel)

theorem negative_transport_368_384 : Transports 368 384 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_368_384
