import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [100,100,100,100,100,100,100,100,104,104,104,104,108,108,108,108]
  130261105881438279277650879277112948528675032697935886362548852706088512839503954990906843780833524405041956402998606825362017491337652652586407544683233 1199147374017265960633291325938063255764503965759265508406894924082726156265357959808194892634967658589052533943767178774272884265945493943907574870018508 98907534543413893069965672729561134927359366219540376083365750659763241386295513541201829716127819896817099562842277835269539785029222791047522397026387 34489820935034801386947586382386611760695349016803462943937882276970804368375833987692198903906444261921599897692083607032022547198693008208683439341119

private def left : Mark := ⟨(-65130552940719139638825439638556474264337516348967943181274426353044256419751977495453421890416762202520978201499303412681008745668826326293203772341617),599573687008632980316645662969031627882251982879632754203447462041363078132678979904097446317483829294526266971883589387136442132972746971953787435009254,(-49453767271706946534982836364780567463679683109770188041682875329881620693147756770600914858063909948408549781421138917634769892514611395523761198513194),(-17244910467517400693473793191193305880347674508401731471968941138485402184187916993846099451953222130960799948846041803516011273599346504104341719670560)⟩
private def right : Mark := ⟨223150408924813429568257078278697684827217164489593706557517903875343655185728975342384684344737312072937481666171912261503779933375528335102582210748462,401412467662013278372076187314746656858369123014675026636293742928533507375474412101625594803649412589135971549054361548108191831140813471407683519226680,(-21672152409049646949491900116252822023413442724699035195215075021236429259215968237235184560719624889902957634611523636048156758945118884214913208687689),(-47679973200031980783861932509880295049930816449115872408810283667599149003917017558013156450602180809053317241821024043891304072454057795942739389225306)⟩

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

theorem positive_transport_576_592 : Transports 576 592 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_576_592
