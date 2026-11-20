import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [108,112,112,112,112,112,112,112,112,108,108,108,108,108,108,104]
  446300817849626859136514156557395369654434328979187413115035807750687310371457950684769368689474624145874963332343824523007559866751056670205164421496924 802824935324026556744152374629493313716738246029350053272587485857067014750948824203251189607298825178271943098108723096216383662281626942815367038453360 43344304818099293898983800232505644046826885449398070390430150042472858518431936474470369121439249779805915269223047272096313517890237768429826417375377 95359946400063961567723865019760590099861632898231744817620567335198298007834035116026312901204361618106634483642048087782608144908115591885478778450611

private def left : Mark := ⟨223150408924813429568257078278697684827217164489593706557517903875343655185728975342384684344737312072937481666171912261503779933375528335102582210748462,401412467662013278372076187314746656858369123014675026636293742928533507375474412101625594803649412589135971549054361548108191831140813471407683519226680,(-21672152409049646949491900116252822023413442724699035195215075021236429259215968237235184560719624889902957634611523636048156758945118884214913208687689),(-47679973200031980783861932509880295049930816449115872408810283667599149003917017558013156450602180809053317241821024043891304072454057795942739389225306)⟩
private def right : Mark := ⟨114818587220579478372919983583748469364868250977402097733269234111145236272996506391493993398281417254855944818780660015700071754248567352347522648860540,(-620560316097046769567327539983737895391176428290181803085634862374491675579078164739982408768876280498674727596028961060517208660922641850674496347155692),52275476941420732616674060397755172461207922902139195246850707564326611867905315157874821361732621170411793246925612580967992905207912747437558528663019,3215049757598415107964087435124561658818614340991380095618265412584332398739167756167742747715316039426946325542876048295906205293620202519402593174966⟩

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

theorem positive_transport_592_608 : Transports 592 608 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_592_608
