import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [96,100,100,100,100,100,104,104,104,104,108,108,108,108,108,108]
  634339257705294490112359137176733503095447992666188225135366933931047196018787176732966323137988273024368588450118364290918255002231047687362686338711 1138015612839976205651305679112526068114928665350968766088591151071667965020287622758834446353430599653624627291771647443504565895261855344569995312122857 100747982019971283327831315733284699409416646191689157747879046173382155817784703102862270682558042848620192466944319668617043659840530786415671192245836 28672151235840682550006342494054107318764353917012380428489904759489496066084699770995340004259474194202999578664771992639837946711955200394016203946514

private def left : Mark := ⟨(-317169628852647245056179568588366751547723996333094112567683466965523598009393588366483161568994136512184294225059182145459127501115523843681343169356),(-569007806419988102825652839556263034057464332675484383044295575535833982510143811379417223176715299826812313645885823721752282947630927672284997656061429),50373991009985641663915657866642349704708323095844578873939523086691077908892351551431135341279021424310096233472159834308521829920265393207835596122918,14336075617920341275003171247027053659382176958506190214244952379744748033042349885497670002129737097101499789332385996319918973355977600197008101973257⟩
private def right : Mark := ⟨(-243505243677906634512295703328860115585648231204928793742660126543453535697066479048458321221849356562470717513579943002920680712943464388325031589718202),(-165167743344822577112891651299471545492285842899009857634818753660307751798687727733656070523193679748809174907282335116965801183102980061141585333175192),27222383351590128769285057498243978635591166240910546814055062325159219546293540024488215239095149530470790670975749483108169801701685656984335796298291,(-44743757989868407221808541010118285332689776476337325617501714582281159381460537309625934563404287619860106302824933733775236463419224474276367906499477)⟩

private theorem cell0 : Transports 544 545 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 544 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 545 546 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 545 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 546 547 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 546 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 547 548 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 547 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 548 549 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 548 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 549 550 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 549 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 550 551 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 550 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 551 552 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 551 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 552 553 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 552 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 553 554 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 553 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 554 555 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 554 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 555 556 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 555 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 556 557 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 556 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 557 558 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 557 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 558 559 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 558 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 559 560 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 559 _ _ (by decide) (by decide +kernel)

theorem positive_transport_544_560 : Transports 544 560 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_544_560
