import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [88,88,88,88,88,88,88,88,88,88,88,88,88,88,88,88]
  259477352810137610133913014187063554661765851538144096516382208511376771090161213012271879154247834512701236952330618940199298690706099913741128342277196 36465807331469539033419930894476195366052566576791789889225342488864903156520799696023692041103491238271247053771294683874229589319772413466202435397616 8779069177053369704200658197136431192312794784049202810060691198373123583610039530754611005883294075154614399275891591437381651961091672418719468532643 104379960155059883202144525940531133970478090505915884483116999840482817912246205763105056334887352257191254073412190943796674319992638830764268863369891

private def left : Mark := ⟨129738676405068805066956507093531777330882925769072048258191104255688385545080606506135939577123917256350618476165309470099649345353049956870564171138598,18232903665734769516709965447238097683026283288395894944612671244432451578260399848011846020551745619135623526885647341937114794659886206733101217698808,(-4389534588526684852100329098568215596156397392024601405030345599186561791805019765377305502941647037577307199637945795718690825980545836209359734266322),(-52189980077529941601072262970265566985239045252957942241558499920241408956123102881552528167443676128595627036706095471898337159996319415382134431684946)⟩
private def right : Mark := ⟨92366808553690568630438911945170436896208835610128953765852682314985879321932005190101745119234209123926355770012885013821800088434911054802735514915235,(-148548916930321626934610705635864201493293189934964603364462235164045910971531288154219586698832191230919841569593718885252968520155375988614808149257759),45282668787932195253815749610238206857602260914178294670190683482658265007646643314790011438508086612379915883066077586382291006443996247560634584505025,(-26316191628715499084351082070893534263546545586108128550305657829383281799192403838842920510528953143707784015948112306314978903761582208065134882063393)⟩

private theorem cell0 : Transports 144 145 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 144 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 145 146 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 145 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 146 147 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 146 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 147 148 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 147 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 148 149 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 148 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 149 150 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 149 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 150 151 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 150 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 151 152 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 151 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 152 153 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 152 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 153 154 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 153 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 154 155 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 154 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 155 156 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 155 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 156 157 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 156 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 157 158 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 157 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 158 159 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 158 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 159 160 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 159 _ _ (by decide) (by decide +kernel)

theorem negative_transport_144_160 : Transports 144 160 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_144_160
