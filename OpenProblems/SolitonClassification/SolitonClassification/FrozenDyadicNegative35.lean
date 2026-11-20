import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [104,100,100,100,100,100,100,100,100,104,104,104,104,108,108,108]
  173125751313691873092939907421853235009301162586550410319787820182790065641385483628622331781548104715400927866747054486298550048859413738285882568859937 1213357911151523737500846029949320393316319280182675593456938306995623080355791044825805406799284555555900996781808390299447863916190256870354359537303072 104341270540604713456223152280055139005358747538296293296713869773237249948930041740983185539234252659850505105374741744875658927381095440719279222489405 9227534858222554243400103137780180647777845952837418690605331564690158413344746518625141694095343185081095715339344437410864695190797395472297509746919

private def left : Mark := ⟨(-86562875656845936546469953710926617504650581293275205159893910091395032820692741814311165890774052357700463933373527243149275024429706869142941284429969),606678955575761868750423014974660196658159640091337796728469153497811540177895522412902703399642277777950498390904195149723931958095128435177179768651536,(-52170635270302356728111576140027569502679373769148146648356934886618624974465020870491592769617126329925252552687370872437829463690547720359639611244703),(-4613767429111277121700051568890090323888922976418709345302665782345079206672373259312570847047671592540547857669672218705432347595398697736148754873460)⟩
private def right : Mark := ⟨212636033335425381867391283741170275790556748928466772096981289900617103938059199091577990011473521109652789937105575235683608942734358753142912637783274,466045891423547961493660779875538325327496147908687627791066784047283138911507214321530081361140413496165075350686208485643642942761354824133262631093987,(-39207542298558736426501519354735644251700998563277472896071185255494469443085481819584758328621940543606055802989012598118338780101925849988092177621795),(-34725072516894357907924500856753098970709068372120267364113240648818322522945999172725205153475950098784829164401068520327245610303867029044326956263119)⟩

private theorem cell0 : Transports 560 561 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 560 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 561 562 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 561 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 562 563 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 562 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 563 564 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 563 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 564 565 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 564 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 565 566 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 565 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 566 567 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 566 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 567 568 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 567 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 568 569 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 568 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 569 570 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 569 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 570 571 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 570 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 571 572 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 571 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 572 573 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 572 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 573 574 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 573 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 574 575 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 574 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 575 576 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 575 _ _ (by decide) (by decide +kernel)

theorem negative_transport_560_576 : Transports 560 576 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_560_576
