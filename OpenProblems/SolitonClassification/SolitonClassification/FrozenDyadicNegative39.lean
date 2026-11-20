import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [108,108,104,104,104,104,100,100,100,100,104,104,104,108,108,108]
  322604318499383260186543777670213726318018035950814259643040106755406689685443808312160053705629663972256550113867401848383337970591839957541052795186351 1264470174603672482727682093681103773529882801362963995643174265692295893096378207868471327267260123952526659051777118524717487597461861051032600632818112 98575636213005328818629900604263457666683976370258709683135584177679538663077814250645774301332241495927426469823726980393734311511506222315660577940997 35427278794575936237869329780163703546989767877108335644253571244035826660546938176839622365265683471453397238777605750369564060618462127627054266051049

private def left : Mark := ⟨(-161302159249691630093271888835106863159009017975407129821520053377703344842721904156080026852814831986128275056933700924191668985295919978770526397593176),632235087301836241363841046840551886764941400681481997821587132846147946548189103934235663633630061976263329525888559262358743798730930525516300316409056,(-49287818106502664409314950302131728833341988185129354841567792088839769331538907125322887150666120747963713234911863490196867155755753111157830288970499),(-17713639397287968118934664890081851773494883938554167822126785622017913330273469088419811182632841735726698619388802875184782030309231063813527133025525)⟩
private def right : Mark := ⟨178779580508608869566247713777730258117727926001156538290664696003664624616435780267905590384400957496362430760574297371724652479061435051829375890156335,635183880152618440335951934729127530649741988360045443689612393454781752932464622019202444769219101350304284235166468580269906957803391977999454319498905,(-47747442678633460125264594105837867641335780086809300000451738981615511972215636212927958653340509899418882122059991583292155657969921687854423473074014),(-21523098105232348912549201395355557308390712990778217560431403003305245496419847704941661723600582831679437050639080872850730639473501981876927073647931)⟩

private theorem cell0 : Transports 624 625 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 624 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 625 626 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 625 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 626 627 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 626 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 627 628 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 627 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 628 629 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 628 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 629 630 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 629 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 630 631 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 630 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 631 632 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 631 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 632 633 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 632 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 633 634 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 633 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 634 635 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 634 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 635 636 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 635 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 636 637 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 636 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 637 638 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 637 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 638 639 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 638 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 639 640 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 639 _ _ (by decide) (by decide +kernel)

theorem negative_transport_624_640 : Transports 624 640 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_624_640
