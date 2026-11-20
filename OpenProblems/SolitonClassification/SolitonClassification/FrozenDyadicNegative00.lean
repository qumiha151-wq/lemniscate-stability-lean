import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [72,72,72,72,72,72,72,72,72,72,72,72,72,72,72,72]
  26187124863169134960105517574620793217733136368344518315866330944769070371237396439066160738607233257207093473020480568073738052367083144426628220715007 0 104748499452676539840422070298483172870932545473378073263465323779076281484949585756264642954428933028828373892081922272294952209468332577706512882860032 0

private def left : Mark := ⟨(-13093562431584567480052758787310396608866568184172259157933165472384535185618698219533080369303616628603546736510240284036869026183541572213314110357504),0,52374249726338269920211035149241586435466272736689036631732661889538140742474792878132321477214466514414186946040961136147476104734166288853256441430016,0⟩
private def right : Mark := ⟨(-19564104589871045944042203090396923926080615857767681922660166751589452304241378320401133021152186279104465993955351624433505592565700938477032443158840),(-25765260705338283008765033185290602915290697256849924677473933495777506684568537772056664829852509089236015750206323224340501392205934358298684623693802),51819890578015192684721432022111267774965244139295520428452507644619596709656545862205690164039542408453703571031453643983935959670552729798549861136203,(-7600064136530467531832495800076547207911750458070965589083245080436145938837004216321408438863323707932969340409300309673674244661907649564991366626947)⟩

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

theorem negative_transport_0_16 : Transports 0 16 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_0_16
