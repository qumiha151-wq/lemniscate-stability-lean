import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [108,108,112,112,112,112,112,112,112,112,112,112,112,112,108,108]
  380129745617773105521271016490651123382484785924577123986226570936527825954059885525256795175625754962060222316452448386544109882121111278753518351264923 1148641702652176911683605384557642312394774516918008076553333491329986467446540975886108742979521094508827387497312654400811726624527945980266722501239827 88054961650658222228328355446387381583134965414014042573797590259918924427368056548017136073291817897320406046102245405962527493284514420960352699082294 56732458665991968251409763574912825592849040115657335691082313434505858472500415323351785596555885956815598336719200570274833223352698363018774484633297

private def left : Mark := ⟨(-190064872808886552760635508245325561691242392962288561993113285468263912977029942762628397587812877481030111158226224193272054941060555639376759175632462),(-574320851326088455841802692278821156197387258459004038276666745664993233723270487943054371489760547254413693748656327200405863312263972990133361250619914),44027480825329111114164177723193690791567482707007021286898795129959462213684028274008568036645908948660203023051122702981263746642257210480176349541147,(-28366229332995984125704881787456412796424520057828667845541156717252929236250207661675892798277942978407799168359600285137416611676349181509387242316649)⟩
private def right : Mark := ⟨(-161302159249691630093271888835106863159009017975407129821520053377703344842721904156080026852814831986128275056933700924191668985295919978770526397593176),632235087301836241363841046840551886764941400681481997821587132846147946548189103934235663633630061976263329525888559262358743798730930525516300316409056,(-49287818106502664409314950302131728833341988185129354841567792088839769331538907125322887150666120747963713234911863490196867155755753111157830288970499),(-17713639397287968118934664890081851773494883938554167822126785622017913330273469088419811182632841735726698619388802875184782030309231063813527133025525)⟩

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

theorem negative_transport_608_624 : Transports 608 624 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_608_624
