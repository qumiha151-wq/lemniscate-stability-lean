import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [100,100,100,100,100,104,104,104,104,104,104,104,104,104,104,104]
  234094597743532777978644304667995162955047697390348413842284910560612180483329216465674149703706253709467871782359551062276118631990876814212255616913611 810756573210698207538925371706169666337535495236170726782330143020138106743002076487780957878864560992800752951954256916557886744857865551011180689125983 98381069809367162526799691328618319055736728958836532314760812049120174487615272417412324107698729059043876929227756442665953998238910200606293642860986 35964054843020723900955913307780740257973891130343447725078330879465910692086214421176467290418663548798481425162944666641080888411914290012647093821191

private def left : Mark := ⟨(-117047298871766388989322152333997581477523848695174206921142455280306090241664608232837074851853126854733935891179775531138059315995438407106127808456806),(-405378286605349103769462685853084833168767747618085363391165071510069053371501038243890478939432280496400376475977128458278943372428932775505590344562992),49190534904683581263399845664309159527868364479418266157380406024560087243807636208706162053849364529521938464613878221332976999119455100303146821430493,(-17982027421510361950477956653890370128986945565171723862539165439732955346043107210588233645209331774399240712581472333320540444205957145006323546910596)⟩
private def right : Mark := ⟨(-199779641185415334873048724560326701428481325130182963858731647318535779192106482049936037680395507386126589079562893712242034889240265045281690761695939),209379120756399659662664637030925134122936810321690582341555520348587379535262135226372897000968789795130501940026087683923251833608147357811726220561909,(-27469283836962790605308522891604597113467704959024512592737476342392738422662276665104156312633134880682299807662728292181438536361551687970865523680981),(-44592605663733299381875541069811098664949968345624242903848409194017022397081700171327101751396225603827471038874654413992900202192041935074313042222809)⟩

private theorem cell0 : Transports 384 385 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 384 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 385 386 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 385 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 386 387 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 386 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 387 388 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 387 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 388 389 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 388 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 389 390 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 389 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 390 391 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 390 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 391 392 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 391 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 392 393 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 392 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 393 394 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 393 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 394 395 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 394 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 395 396 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 395 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 396 397 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 396 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 397 398 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 397 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 398 399 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 398 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 399 400 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 399 _ _ (by decide) (by decide +kernel)

theorem negative_transport_384_400 : Transports 384 400 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_384_400
