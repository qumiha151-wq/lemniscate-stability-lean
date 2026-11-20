import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [108,108,108,108,108,108,108,108,108,108,108,104,104,104,104,100]
  487010487355813269024591406657720231171296462409857587485320253086907071394132958096916642443698713124941435027159886005841361425886928776650063179436403 330335486689645154225783302598943090984571685798019715269637507320615503597375455467312141046387359497618349814564670233931602366205960122283170666350383 54444766703180257538570114996487957271182332481821093628110124650318439092587080048976430478190299060941581341951498966216339603403371313968671592596582 89487515979736814443617082020236570665379552952674651235003429164562318762921074619251869126808575239720212605649867467550472926838448948552735812998953

private def left : Mark := ⟨(-243505243677906634512295703328860115585648231204928793742660126543453535697066479048458321221849356562470717513579943002920680712943464388325031589718202),(-165167743344822577112891651299471545492285842899009857634818753660307751798687727733656070523193679748809174907282335116965801183102980061141585333175192),27222383351590128769285057498243978635591166240910546814055062325159219546293540024488215239095149530470790670975749483108169801701685656984335796298291,(-44743757989868407221808541010118285332689776476337325617501714582281159381460537309625934563404287619860106302824933733775236463419224474276367906499477)⟩
private def right : Mark := ⟨(-65130552940719139638825439638556474264337516348967943181274426353044256419751977495453421890416762202520978201499303412681008745668826326293203772341617),599573687008632980316645662969031627882251982879632754203447462041363078132678979904097446317483829294526266971883589387136442132972746971953787435009254,(-49453767271706946534982836364780567463679683109770188041682875329881620693147756770600914858063909948408549781421138917634769892514611395523761198513194),(-17244910467517400693473793191193305880347674508401731471968941138485402184187916993846099451953222130960799948846041803516011273599346504104341719670560)⟩

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

theorem positive_transport_560_576 : Transports 560 576 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_560_576
