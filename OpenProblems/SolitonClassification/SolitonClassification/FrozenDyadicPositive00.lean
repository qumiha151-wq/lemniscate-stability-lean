import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [76,76,76,76,76,76,76,76,76,76,76,76,76,76,76,76]
  104748499452676539840422070298483172870932545473378073263465323779076281484949585756264642954428933028828373892081922272294952209468332577706512882860032 0 104748499452676539840422070298483172870932545473378073263465323779076281484949585756264642954428933028828373892081922272294952209468332577706512882860032 0

private def left : Mark := ⟨52374249726338269920211035149241586435466272736689036631732661889538140742474792878132321477214466514414186946040961136147476104734166288853256441430016,0,52374249726338269920211035149241586435466272736689036631732661889538140742474792878132321477214466514414186946040961136147476104734166288853256441430016,0⟩
private def right : Mark := ⟨42963177940536758217251025350408783374557004554795242608485091944968760924864322899669551766900589531246646087046714398084501588553156881653873402683261,(-36135795319814003575304758584259864606171692653138142535753224220015679905964729076676878944729829947952595555532379691897518131266531262813039575464979),46705911299614220605206655047096999004753943331068095425311886483722625856216229355791448408860126417877496935952956951991959602894439186051443507469422,23698520714791735878227098621436468035927731811064167795192195953443261221665228945675111426388089812360450725867150053096763701989947226588814120000302⟩

private theorem cell0 : Transports 0 1 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 0 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 1 2 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 1 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 2 3 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 2 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 3 4 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 3 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 4 5 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 4 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 5 6 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 5 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 6 7 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 6 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 7 8 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 7 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 8 9 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 8 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 9 10 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 9 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 10 11 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 10 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 11 12 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 11 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 12 13 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 12 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 13 14 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 13 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 14 15 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 14 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 15 16 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 15 _ _ (by decide) (by decide +kernel)

theorem positive_transport_0_16 : Transports 0 16 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_0_16
