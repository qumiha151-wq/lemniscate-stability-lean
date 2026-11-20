import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [88,88,88,88,88,88,84,84,84,84,84,84,84,84,84,84]
  184733617107381137260877823890340873792417671220257907531705364629971758643864010380203490238468418247852711540025770027643600176869822109605471029830470 297097833860643253869221411271728402986586379869929206728924470328091821943062576308439173397664382461839683139187437770505937040310751977229616298515517 90565337575864390507631499220476413715204521828356589340381366965316530015293286629580022877016173224759831766132155172764582012887992495121269169010050 52632383257430998168702164141787068527093091172216257100611315658766563598384807677685841021057906287415568031896224612629957807523164416130269764126785

private def left : Mark := ⟨92366808553690568630438911945170436896208835610128953765852682314985879321932005190101745119234209123926355770012885013821800088434911054802735514915235,(-148548916930321626934610705635864201493293189934964603364462235164045910971531288154219586698832191230919841569593718885252968520155375988614808149257759),45282668787932195253815749610238206857602260914178294670190683482658265007646643314790011438508086612379915883066077586382291006443996247560634584505025,(-26316191628715499084351082070893534263546545586108128550305657829383281799192403838842920510528953143707784015948112306314978903761582208065134882063393)⟩
private def right : Mark := ⟨3973856866437808556611130274829610186160443186443636322038068083655596707521799376403276735448427821732919417401901584857978591483651101474901251248302,(-194100317980380620812531489710225736021735411825964504923747771225211123481275337336603249657458375898180043032932072282557275879715491914930814423252418),52309632147147437693518293832217310512683333505717942730112634428152085631981666105241486756544123083730298226209445991122800032888517432871202925157222,(-2600849674041867609657258812164498734204405066502498892272666768406230936822157052520787858255609879968915483415424522304872669660367431724448384790530)⟩

private theorem cell0 : Transports 160 161 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 160 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 161 162 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 161 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 162 163 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 162 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 163 164 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 163 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 164 165 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 164 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 165 166 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 165 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 166 167 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 166 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 167 168 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 167 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 168 169 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 168 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 169 170 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 169 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 170 171 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 170 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 171 172 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 171 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 172 173 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 172 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 173 174 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 173 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 174 175 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 174 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 175 176 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 175 _ _ (by decide) (by decide +kernel)

theorem negative_transport_160_176 : Transports 160 176 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_160_176
