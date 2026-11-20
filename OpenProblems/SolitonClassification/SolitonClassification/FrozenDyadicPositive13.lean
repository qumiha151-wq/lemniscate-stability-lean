import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [92,92,92,92,92,92,92,96,96,96,96,96,96,96,96,96]
  228228569240515191321503272593484918914030446848900859357041310887618438898093627741135205295591194327790705272193167001756708818191080014496759080012171 393306672750327101703211118211220744741860334480151544837676051741173707347823893281906279284368789055482637964199285774806400576490505717688117026714263 104039463280491092547054909919080141723603469546032543721026722242065636428629564701358131390135248082887992104322963748348142838877134703434750261590038 12167095705003844428288294226305851390473468231784477145882134276885727574321725728563846303390243504461661414874214471972396982282777558848128543934787

private def left : Mark := ⟨(-114114284620257595660751636296742459457015223424450429678520655443809219449046813870567602647795597163895352636096583500878354409095540007248379540006086),(-196653336375163550851605559105610372370930167240075772418838025870586853673911946640953139642184394527741318982099642887403200288245252858844058513357132),52019731640245546273527454959540070861801734773016271860513361121032818214314782350679065695067624041443996052161481874174071419438567351717375130795019,(-6083547852501922214144147113152925695236734115892238572941067138442863787160862864281923151695121752230830707437107235986198491141388779424064271967394)⟩
private def right : Mark := ⟨(-154538509112794182672827671680455913314041178763194590342303276956959337816444810006604980163344579309591376854101302967476654032938500590553096022844823),78397199816620721140391111755581802013913635094181805164133399644198036845271394147464922596532988265404391110217111735059883984280276716778534929208705,3046571733305621660442263205528446466053717315519077998446880743242195989783207070054998076084231796587344059011548812377361270788891483951131476886513,(-52285566221192130470477495569279257060421005747738083120844075448639679295429352579871752787082838487939818036786901406020625205199870126640858526490614)⟩

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

theorem positive_transport_208_224 : Transports 208 224 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_208_224
