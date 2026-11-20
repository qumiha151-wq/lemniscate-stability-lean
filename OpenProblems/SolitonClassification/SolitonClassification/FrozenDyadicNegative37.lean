import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [104,104,104,104,100,100,100,100,100,104,104,104,104,108,108,108]
  264266484265639743829446219014124890497196578206550378593656253054041448478590579740626675298462804923411522300843370452162702909161511940917050272172834 1245859961621708435639489502776047496126917845934103847422941742382182208877850589132145980836809654914464049204597506724405812569947780222016712736032639 100440798907788474804368369496882174166048233986819706976267236659766845731482269681833207116756547115729969936114345698894346482187808155771807466824698 29730355738749156334903093029843969513573376098256522696722441056052442463212288987186221681285268593851700624416044517284015070578201889390610994739267

private def left : Mark := ⟨132133242132819871914723109507062445248598289103275189296828126527020724239295289870313337649231402461705761150421685226081351454580755970458525136086417,(-622929980810854217819744751388023748063458922967051923711470871191091104438925294566072990418404827457232024602298753362202906284973890111008356368016320),50220399453894237402184184748441087083024116993409853488133618329883422865741134840916603558378273557864984968057172849447173241093904077885903733412349,(-14865177869374578167451546514921984756786688049128261348361220528026221231606144493593110840642634296925850312208022258642007535289100944695305497369634)⟩
private def right : Mark := ⟨(-190064872808886552760635508245325561691242392962288561993113285468263912977029942762628397587812877481030111158226224193272054941060555639376759175632462),(-574320851326088455841802692278821156197387258459004038276666745664993233723270487943054371489760547254413693748656327200405863312263972990133361250619914),44027480825329111114164177723193690791567482707007021286898795129959462213684028274008568036645908948660203023051122702981263746642257210480176349541147,(-28366229332995984125704881787456412796424520057828667845541156717252929236250207661675892798277942978407799168359600285137416611676349181509387242316649)⟩

private theorem cell0 : Transports 592 593 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 592 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 593 594 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 593 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 594 595 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 594 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 595 596 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 595 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 596 597 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 596 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 597 598 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 597 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 598 599 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 598 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 599 600 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 599 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 600 601 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 600 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 601 602 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 601 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 602 603 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 602 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 603 604 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 603 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 604 605 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 604 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 605 606 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 605 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 606 607 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 606 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 607 608 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 607 _ _ (by decide) (by decide +kernel)

theorem negative_transport_592_608 : Transports 592 608 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_592_608
