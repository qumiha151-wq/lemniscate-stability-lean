import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [96,96,96,96,92,92,92,92,92,92,92,92,92,92,92,88]
  309077018225588365345655343360911826628082357526389180684606553913918675632889620013209960326689158619182753708202605934953308065877001181106192045689645 156794399633241442280782223511163604027827270188363610328266799288396073690542788294929845193065976530808782220434223470119767968560553433557069858417410 6093143466611243320884526411056892932107434631038155996893761486484391979566414140109996152168463593174688118023097624754722541577782967902262953773026 104571132442384260940954991138558514120842011495476166241688150897279358590858705159743505574165676975879636073573802812041250410399740253281717052981227

private def left : Mark := ⟨(-154538509112794182672827671680455913314041178763194590342303276956959337816444810006604980163344579309591376854101302967476654032938500590553096022844823),78397199816620721140391111755581802013913635094181805164133399644198036845271394147464922596532988265404391110217111735059883984280276716778534929208705,3046571733305621660442263205528446466053717315519077998446880743242195989783207070054998076084231796587344059011548812377361270788891483951131476886513,(-52285566221192130470477495569279257060421005747738083120844075448639679295429352579871752787082838487939818036786901406020625205199870126640858526490614)⟩
private def right : Mark := ⟨(-58924144543602055219788084137432770017728893397756241983661515138865632350309307295396171572575316004543989323728661449821424949956561889844161807546910),250656332336307949522729197540286447825991452142628073844961130257089104671801896424053276365677878070855102384983240085076705233812239666154700774067624,(-44839565334700691087029548609775286792136686148310940871549105571566459090904027598441752279022413659616539153730080710256030849913805051005918898039633),(-27064283012707956134628786558310391748901670298082497295250964551670262879800017014623964560465158950599018596634738128009169665827649401410319672475290)⟩

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

theorem positive_transport_224_240 : Transports 224 240 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_224_240
