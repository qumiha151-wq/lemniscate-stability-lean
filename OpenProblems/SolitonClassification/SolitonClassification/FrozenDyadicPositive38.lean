import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [104,104,104,100,100,100,100,100,100,104,104,104,104,108,108,108]
  229637174441158956745839967167496938729736501954804195466538468222290472545993012782987986796562834509711889637561320031400143508497134704695045297721080 1241120632194093539134655079967475790782352856580363606171269724748983351158156329479964817537752560997349455192057922121034417321845283701348992694311383 104550953882841465233348120795510344922415845804278390493701415128653223735810630315749642723465242340823586493851225161935985810415825494875117057326038 6430099515196830215928174870249123317637228681982760191236530825168664797478335512335485495430632078853892651085752096591812410587240405038805186349932

private def left : Mark := ⟨114818587220579478372919983583748469364868250977402097733269234111145236272996506391493993398281417254855944818780660015700071754248567352347522648860540,(-620560316097046769567327539983737895391176428290181803085634862374491675579078164739982408768876280498674727596028961060517208660922641850674496347155692),52275476941420732616674060397755172461207922902139195246850707564326611867905315157874821361732621170411793246925612580967992905207912747437558528663019,3215049757598415107964087435124561658818614340991380095618265412584332398739167756167742747715316039426946325542876048295906205293620202519402593174966⟩
private def right : Mark := ⟨(-199763529490240289240775036208018697284646811921098686362955471875984635296958313743028969835187916528428396435115904708860436022393302899691257816190818),(-536770618044297616232272610643960996929694391958164697195187362221491119862199242718486517050537069274802733291933608753542977443322322040002282495141278),48984723930115196818817120468308726922610291705235864011236158460221081378652483414877864202920388896276850697305409984042188802993805167701286961476085,(-18535340727573473122965489504822757890352637416416186562212711452365888321625908288302169772601619836393576367726343822882429712094958155572977235614867)⟩

private theorem cell0 : Transports 608 609 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 608 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 609 610 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 609 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 610 611 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 610 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 611 612 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 611 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 612 613 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 612 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 613 614 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 613 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 614 615 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 614 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 615 616 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 615 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 616 617 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 616 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 617 618 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 617 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 618 619 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 618 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 619 620 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 619 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 620 621 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 620 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 621 622 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 621 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 622 623 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 622 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 623 624 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 623 _ _ (by decide) (by decide +kernel)

theorem positive_transport_608_624 : Transports 608 624 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_608_624
