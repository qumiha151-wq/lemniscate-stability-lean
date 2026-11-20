import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [76,76,76,76,76,76,76,76,76,76,76,76,76,76,76,76]
  85926355881073516434502050700817566749114009109590485216970183889937521849728645799339103533801179062493292174093428796169003177106313763307746805366522 72271590639628007150609517168519729212343385306276285071506448440031359811929458153353757889459659895905191111064759383795036262533062525626079150929957 93411822599228441210413310094193998009507886662136190850623772967445251712432458711582896817720252835754993871905913903983919205788878372102887014938844 47397041429583471756454197242872936071855463622128335590384391906886522443330457891350222852776179624720901451734300106193527403979894453177628240000604

private def left : Mark := ⟨42963177940536758217251025350408783374557004554795242608485091944968760924864322899669551766900589531246646087046714398084501588553156881653873402683261,(-36135795319814003575304758584259864606171692653138142535753224220015679905964729076676878944729829947952595555532379691897518131266531262813039575464979),46705911299614220605206655047096999004753943331068095425311886483722625856216229355791448408860126417877496935952956951991959602894439186051443507469422,23698520714791735878227098621436468035927731811064167795192195953443261221665228945675111426388089812360450725867150053096763701989947226588814120000302⟩
private def right : Mark := ⟨18354155352165603324090303226030554984824744921969032201250182832980540920556323727581454990767466973811657840161236046553078973440662290264439554353799,(-60382470018674753218332313614541485795434941863279683972568169694376307491063337130483848003239989419449270442628948295070544663622190232309200387847693),37533453663749337561064620519573415635388819393459116919239188624938450850674153551228464116036080638040627218737999286275031924859054857970225832426673,36528097274126197919110123623273768268531863585591769174487191240622756140132765157437745170690685452807598552278831362675026920061187239565567179795920⟩

private theorem cell0 : Transports 16 17 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 16 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 17 18 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 17 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 18 19 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 18 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 19 20 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 19 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 20 21 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 20 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 21 22 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 21 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 22 23 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 22 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 23 24 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 23 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 24 25 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 24 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 25 26 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 25 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 26 27 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 26 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 27 28 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 27 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 28 29 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 28 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 29 30 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 29 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 30 31 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 30 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 31 32 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 31 _ _ (by decide) (by decide +kernel)

theorem positive_transport_16_32 : Transports 16 32 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_16_32
