import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [108,108,112,112,112,112,112,112,112,112,112,108,108,108,108,108]
  425272066670850763734782567482340551581113497856933544193962579801234207876118398183155980022947042219305579874211150471367217885468717506285825275566548 932091782847095922987321559751076650654992295817375255582133568094566277823014428643060162722280826992330150701372416971287285885522709648266525262187974 78415084597117472853003038709471288503401997126554945792142370510988938886170963639169516657243881087212111605978025196236677560203851699976184355243589 69450145033788715815849001713506197941418136744240534728226481297636645045891998345450410306951900197569658328802137040654491220607734058088653912526237

private def left : Mark := ⟨212636033335425381867391283741170275790556748928466772096981289900617103938059199091577990011473521109652789937105575235683608942734358753142912637783274,466045891423547961493660779875538325327496147908687627791066784047283138911507214321530081361140413496165075350686208485643642942761354824133262631093987,(-39207542298558736426501519354735644251700998563277472896071185255494469443085481819584758328621940543606055802989012598118338780101925849988092177621795),(-34725072516894357907924500856753098970709068372120267364113240648818322522945999172725205153475950098784829164401068520327245610303867029044326956263119)⟩
private def right : Mark := ⟨132133242132819871914723109507062445248598289103275189296828126527020724239295289870313337649231402461705761150421685226081351454580755970458525136086417,(-622929980810854217819744751388023748063458922967051923711470871191091104438925294566072990418404827457232024602298753362202906284973890111008356368016320),50220399453894237402184184748441087083024116993409853488133618329883422865741134840916603558378273557864984968057172849447173241093904077885903733412349,(-14865177869374578167451546514921984756786688049128261348361220528026221231606144493593110840642634296925850312208022258642007535289100944695305497369634)⟩

private theorem cell0 : Transports 576 577 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 576 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 577 578 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 577 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 578 579 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 578 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 579 580 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 579 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 580 581 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 580 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 581 582 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 581 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 582 583 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 582 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 583 584 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 583 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 584 585 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 584 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 585 586 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 585 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 586 587 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 586 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 587 588 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 587 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 588 589 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 588 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 589 590 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 589 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 590 591 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 590 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 591 592 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 591 _ _ (by decide) (by decide +kernel)

theorem negative_transport_576_592 : Transports 576 592 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_576_592
