import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [80,80,80,80,80,80,80,80,80,80,80,80,80,80,80,80]
  158783439374922025714154906705687207646038720820953370556014222539915457427111040388020117597886885005480543175745341393090105326662697448636085744865101 101716802809524605177491021279883771417624551181228057883003694656515072175305299562367686878270497549325832811006140447940640103792020024007689164683942 82283881464591426101984755551030077272721623901770167902581465141502027222357018114519101998589888750616907069635341985997400069613584673660348229669185 64819834840181789163246125207563751395853308730868377678229854996033053663820947303540416921141025951905888740518545935821528850293401424980435511008893

private def left : Mark := ⟨(-79391719687461012857077453352843603823019360410476685278007111269957728713555520194010058798943442502740271587872670696545052663331348724318042872432551),50858401404762302588745510639941885708812275590614028941501847328257536087652649781183843439135248774662916405503070223970320051896010012003844582341971,(-41141940732295713050992377775515038636360811950885083951290732570751013611178509057259550999294944375308453534817670992998700034806792336830174114834593),(-32409917420090894581623062603781875697926654365434188839114927498016526831910473651770208460570512975952944370259272967910764425146700712490217755504447)⟩
private def right : Mark := ⟨(-40451859503201517116714582394121833076413840779328576224302135275774066843844615667942025493466082108979765344472008236033740649960743413408011995944400),98971361327358073022317467443627581100642396180814949974319698321176354718952675303305353998336772472630610313683999645056354306863593955994525387024052,(-52222547635905244799049695897122843518348353242759140551026510747798717740081218934886574372423968201440125202426916006250742410903848055684409516359154),(-3983409696786393715966989117275351308687151689124891046814345010297516337584816326553529824305246892813029393052445156401689093115143573115068674622070)⟩

private theorem cell0 : Transports 80 81 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 80 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 81 82 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 81 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 82 83 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 82 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 83 84 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 83 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 84 85 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 84 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 85 86 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 85 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 86 87 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 86 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 87 88 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 87 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 88 89 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 88 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 89 90 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 89 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 90 91 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 90 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 91 92 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 91 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 92 93 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 92 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 93 94 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 93 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 94 95 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 94 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 95 96 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 95 _ _ (by decide) (by decide +kernel)

theorem negative_transport_80_96 : Transports 80 96 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_80_96
