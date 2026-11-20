import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [96,96,96,92,92,92,92,92,92,92,92,92,92,96,96,96]
  188594437046928432998093223107193110324443630398870230532047710383878792853024253749205567586943653136425820843298685958121304268213236609404472994022047 677743480524909107641115147097345377618546896423290012115400577632573174040613567771042112882945621236005589056270937754027787988341412610017956041865760 86884474177958566194760504468192883687501878281904977378273271921543601479969763509281364819174300920501491002231813975811340813095480523851774722729417 58509283745462381959770061869995676379712448705247533646543499453458695105735103625882286047835550453306752454202588199147426041935547546884619671712197

private def left : Mark := ⟨(-94297218523464216499046611553596555162221815199435115266023855191939396426512126874602783793471826568212910421649342979060652134106618304702236497011024),338871740262454553820557573548672688809273448211645006057700288816286587020306783885521056441472810618002794528135468877013893994170706305008978020932880,(-43442237088979283097380252234096441843750939140952488689136635960771800739984881754640682409587150460250745501115906987905670406547740261925887361364709),(-29254641872731190979885030934997838189856224352623766823271749726729347552867551812941143023917775226653376227101294099573713020967773773442309835856099)⟩
private def right : Mark := ⟨85399924617814865383505717827277845004215477476388593774085225271595855839943548757798332389934644524838279454095413785860080490575754640045787432681578,366506388540493156696149493405860993189275815773860281052702675980660098343100643648618620756923612979730458725676493844639130050434524100689885261268586,(-44932089053874433854673741928653003137179349371409275869773520368052233643346341242175488744601511875267812316138465454835153217480850901948442417835523),(-26910395902913461692167040299799654819161037103800618935909797716943443120985664176596640335624982131200125765897367841059252068978897806229314178897090)⟩

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

theorem positive_transport_336_352 : Transports 336 352 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_336_352
