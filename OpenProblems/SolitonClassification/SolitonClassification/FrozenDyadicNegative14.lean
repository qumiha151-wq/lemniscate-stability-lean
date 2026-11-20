import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [92,88,88,88,88,88,88,88,88,88,88,88,88,88,88,88]
  151231037142848279062510703056473254884879108219143401826878363744055586949318979825342527455871578751201065585354541781939244777534314582026187124669935 470636930786099899029196538656492604761996896229393659418394370136936363849835484284081740561485243697148370116711089907044786822196615255743071963861712 103096289466192687326118244080867018582039496571924521593886503112655464219692094545016615253334261130179051717174084634466873077638471945207639289126685 18531142325566012031605367764057561567293389184862356173104685901988625202859889624353277378314914949743155100402812108044850655604295260697433862791537

private def left : Mark := ⟨(-75615518571424139531255351528236627442439554109571700913439181872027793474659489912671263727935789375600532792677270890969622388767157291013093562334968),235318465393049949514598269328246302380998448114696829709197185068468181924917742142040870280742621848574185058355544953522393411098307627871535981930856,(-51548144733096343663059122040433509291019748285962260796943251556327732109846047272508307626667130565089525858587042317233436538819235972603819644563343),(-9265571162783006015802683882028780783646694592431178086552342950994312601429944812176638689157457474871577550201406054022425327802147630348716931395769)⟩
private def right : Mark := ⟨51226316167668213657647916030791260140565433986728829245616243278542615509311959793967563814170122705788616574239377233146386414887349328162196359086363,266439817596819336185505206826934830818259472861369154447449514706053868785354998588467365467746529110504071174572632837212871263960756075971754036718501,(-52309409022408332059270360091186711314914894179994332879025847168502518950935907359055158224708575087179343711388436680471529732643464966413986091228918),(-2605333399630482558072456600154549831503241161667355230450370804576211328473699111893355382753525661312027248335297936847982057783816295505541958931155)⟩

private theorem cell0 : Transports 224 225 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 224 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 225 226 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 225 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 226 227 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 226 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 227 228 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 227 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 228 229 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 228 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 229 230 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 229 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 230 231 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 230 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 231 232 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 231 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 232 233 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 232 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 233 234 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 233 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 234 235 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 234 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 235 236 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 235 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 236 237 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 236 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 237 238 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 237 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 238 239 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 238 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 239 240 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 239 _ _ (by decide) (by decide +kernel)

theorem negative_transport_224_240 : Transports 224 240 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_224_240
