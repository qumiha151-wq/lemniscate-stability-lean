import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [80,80,80,80,84,84,84,84,84,84,84,84,84,84,84,84]
  119589591528421146450680773528958072990208757428645139254385265421328808979240478419001573155753681287974405387327523473009332420529082984459017065787511 185848794185544782978058979016938015118262330456620367390663207101022308240246806060767274602545748810535751555211245417926193350049590775544782057989281 95190786281687377480051208607706467921927029445626935788892189204858903645516091425570710726244767906445179052774030014839906785457332232576379275015348 43714555295250294355985206966587660741246133936134838739267825546446041552076288728701935143554622060465303010820369874279878288727131419523531410692946

private def left : Mark := ⟨(-59794795764210573225340386764479036495104378714322569627192632710664404489620239209500786577876840643987202693663761736504666210264541492229508532893756),(-92924397092772391489029489508469007559131165228310183695331603550511154120123403030383637301272874405267875777605622708963096675024795387772391028994641),47595393140843688740025604303853233960963514722813467894446094602429451822758045712785355363122383953222589526387015007419953392728666116288189637507674,21857277647625147177992603483293830370623066968067419369633912773223020776038144364350967571777311030232651505410184937139939144363565709761765705346473⟩
private def right : Mark := ⟨(-102368520860695556278542771230755483255840888104036883495239134543232075149729075443605781651110488104402688803565449043789798705033678033825917699772028),(-64208510332894133575671038045347225497707944574953262409045810598708273074717818686360285745834312982786816783532279260065730518847922284476222188070453),49117583870170859472712612889285912742173436532500291410131394896689534482769399124177945125674324121376627449409783936322552713310093635796235710910414,(-18180346233050011849437283251337548341211686268225037689801521567987383279141421735746040143801345595813978113076462805936030420647812772688322981340309)⟩

private theorem cell0 : Transports 64 65 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 64 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 65 66 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 65 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 66 67 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 66 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 67 68 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 67 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 68 69 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 68 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 69 70 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 69 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 70 71 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 70 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 71 72 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 71 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 72 73 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 72 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 73 74 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 73 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 74 75 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 74 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 75 76 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 75 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 76 77 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 76 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 77 78 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 77 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 78 79 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 78 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 79 80 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 79 _ _ (by decide) (by decide +kernel)

theorem positive_transport_64_80 : Transports 64 80 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_64_80
