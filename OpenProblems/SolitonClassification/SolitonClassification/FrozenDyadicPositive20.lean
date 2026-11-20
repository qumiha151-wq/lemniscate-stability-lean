import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [100,100,100,100,100,100,100,100,100,100,100,96,96,96,96,96]
  374879175128620646989391761756725523267809590446327516190524327711320154937402293650889848919331570458868282099129012983313036478110914844968455725747069 130865577660044551802415430117729302990157757748787908723754249383750554409043201898978418410744158573208587878644223171309628249073868826530054013400309 53165173658967350305321442679376965962130233195944892874970652904276278816573058058692126868574840125913849335815412605797398981799933422315286914978434 90253600744785919990448040170269136132072533156584363696627777093755082732558300410441508898372431154273503771880933609974557897328388529051308175372685

private def left : Mark := ⟨(-187439587564310323494695880878362761633904795223163758095262163855660077468701146825444924459665785229434141049564506491656518239055457422484227862873535),(-65432788830022275901207715058864651495078878874393954361877124691875277204521600949489209205372079286604293939322111585654814124536934413265027006700155),26582586829483675152660721339688482981065116597972446437485326452138139408286529029346063434287420062956924667907706302898699490899966711157643457489217,(-45126800372392959995224020085134568066036266578292181848313888546877541366279150205220754449186215577136751885940466804987278948664194264525654087686343)⟩
private def right : Mark := ⟨(-94297218523464216499046611553596555162221815199435115266023855191939396426512126874602783793471826568212910421649342979060652134106618304702236497011024),338871740262454553820557573548672688809273448211645006057700288816286587020306783885521056441472810618002794528135468877013893994170706305008978020932880,(-43442237088979283097380252234096441843750939140952488689136635960771800739984881754640682409587150460250745501115906987905670406547740261925887361364709),(-29254641872731190979885030934997838189856224352623766823271749726729347552867551812941143023917775226653376227101294099573713020967773773442309835856099)⟩

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

theorem positive_transport_320_336 : Transports 320 336 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_320_336
