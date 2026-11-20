import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [96,96,96,96,92,92,92,92,92,92,92,92,92,92,92,92]
  307639693937053273791703216175457926400567904805090694157595403512095766412330091229398329290765269749691758910874637244709704354689526625638793289449711 53059574094309442542044067157343671178797936559435529032819740257336506650920849074435558162412158397709574647897087281583008381896935146769996330435300 22271779961946547519729507588799504609972061421953403056480384287268520704511310620205678724289940983347432024632308584525465323432171076638677754097557 102353387608393370698535805374608961914251644229975103307769059367884558611418805246726123060082343458034866387694306261364729185545513546135664350721063

private def left : Mark := ⟨(-153819846968526636895851608087728963200283952402545347078797701756047883206165045614699164645382634874845879455437318622354852177344763312819396644724856),26529787047154721271022033578671835589398968279717764516409870128668253325460424537217779081206079198854787323948543640791504190948467573384998165217650,(-11135889980973273759864753794399752304986030710976701528240192143634260352255655310102839362144970491673716012316154292262732661716085538319338877048779),(-51176693804196685349267902687304480957125822114987551653884529683942279305709402623363061530041171729017433193847153130682364592772756773067832175360532)⟩
private def right : Mark := ⟨(-75615518571424139531255351528236627442439554109571700913439181872027793474659489912671263727935789375600532792677270890969622388767157291013093562334968),235318465393049949514598269328246302380998448114696829709197185068468181924917742142040870280742621848574185058355544953522393411098307627871535981930856,(-51548144733096343663059122040433509291019748285962260796943251556327732109846047272508307626667130565089525858587042317233436538819235972603819644563343),(-9265571162783006015802683882028780783646694592431178086552342950994312601429944812176638689157457474871577550201406054022425327802147630348716931395769)⟩

private theorem cell0 : Transports 208 209 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 208 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 209 210 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 209 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 210 211 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 210 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 211 212 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 211 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 212 213 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 212 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 213 214 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 213 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 214 215 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 214 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 215 216 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 215 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 216 217 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 216 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 217 218 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 217 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 218 219 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 218 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 219 220 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 219 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 220 221 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 220 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 221 222 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 221 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 222 223 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 222 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 223 224 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 223 _ _ (by decide) (by decide +kernel)

theorem negative_transport_208_224 : Transports 208 224 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_208_224
