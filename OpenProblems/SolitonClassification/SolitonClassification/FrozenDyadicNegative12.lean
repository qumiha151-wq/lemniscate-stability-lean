import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [92,92,92,92,92,92,92,92,92,92,92,92,96,96,96,96]
  195275236502722364959259450686721555030095652094490686786628811731316294296745381577752042330513802795623356543882647494408451590659150703310969277665583 398754388350014054284525826542341378311428244271661985262318775613229448163309897222522734552678850736170576528193432467836249884779022878255007722010565 92283668866049121428578561970649691800357122993873408655445992347687872573405432722309133917145135993198299354239070667820229682774451101649988333591734 49557770311110380193336621699134364566433595917583897206911656358764613652523229069257942580234599570132646002809783318305776577175113159196450361616195

private def left : Mark := ⟨(-97637618251361182479629725343360777515047826047245343393314405865658147148372690788876021165256901397811678271941323747204225795329575351655484638832792),(-199377194175007027142262913271170689155714122135830992631159387806614724081654948611261367276339425368085288264096716233918124942389511439127503861005283),46141834433024560714289280985324845900178561496936704327722996173843936286702716361154566958572567996599149677119535333910114841387225550824994166795867,(-24778885155555190096668310849567182283216797958791948603455828179382306826261614534628971290117299785066323001404891659152888288587556579598225180808098)⟩
private def right : Mark := ⟨(-153819846968526636895851608087728963200283952402545347078797701756047883206165045614699164645382634874845879455437318622354852177344763312819396644724856),26529787047154721271022033578671835589398968279717764516409870128668253325460424537217779081206079198854787323948543640791504190948467573384998165217650,(-11135889980973273759864753794399752304986030710976701528240192143634260352255655310102839362144970491673716012316154292262732661716085538319338877048779),(-51176693804196685349267902687304480957125822114987551653884529683942279305709402623363061530041171729017433193847153130682364592772756773067832175360532)⟩

private theorem cell0 : Transports 192 193 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 192 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 193 194 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 193 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 194 195 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 194 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 195 196 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 195 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 196 197 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 196 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 197 198 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 197 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 198 199 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 198 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 199 200 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 199 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 200 201 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 200 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 201 202 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 201 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 202 203 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 202 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 203 204 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 203 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 204 205 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 204 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 205 206 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 205 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 206 207 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 206 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 207 208 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 207 _ _ (by decide) (by decide +kernel)

theorem negative_transport_192_208 : Transports 192 208 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_192_208
