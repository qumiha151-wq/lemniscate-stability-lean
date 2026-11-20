import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [88,88,88,88,88,88,88,88,88,88,88,88,88,92,92,92]
  117848289087204110439576168274865540035457786795512483967323030277731264700618614590792343145150632009087978647457322899642849899913123779688323615093819 501312664672615899045458395080572895651982904285256147689922260514178209343603792848106552731355756141710204769966480170153410467624479332309401548135248 89679130669401382174059097219550573584273372296621881743098211143132918181808055196883504558044827319233078307460161420512061699827610102011837796079265 54128566025415912269257573116620783497803340596164994590501929103340525759600034029247929120930317901198037193269476256018339331655298802820639344950579

private def left : Mark := ⟨(-58924144543602055219788084137432770017728893397756241983661515138865632350309307295396171572575316004543989323728661449821424949956561889844161807546910),250656332336307949522729197540286447825991452142628073844961130257089104671801896424053276365677878070855102384983240085076705233812239666154700774067624,(-44839565334700691087029548609775286792136686148310940871549105571566459090904027598441752279022413659616539153730080710256030849913805051005918898039633),(-27064283012707956134628786558310391748901670298082497295250964551670262879800017014623964560465158950599018596634738128009169665827649401410319672475290)⟩
private def right : Mark := ⟨72997548153175823214105677468684313418602114902533170140430916987823514030181544166870592609432165124619860311527741745878644720832818660519249838538269,271405297255641816157924056819453548705970033414467539527998797115596783059200614176745312357232407005543141700217892717772366249189970072267336624820262,(-43183826210094871009729225955113772849628495087972637871517019526983186073778990132949710046829721401506056189523905374358370919569504154400731392304557),(-29634763171875823025708563262569685451093816818536299886702348862827945038802912059747372727976793563793958634422119259221038132787310992805228237353157)⟩

private theorem cell0 : Transports 240 241 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 240 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 241 242 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 241 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 242 243 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 242 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 243 244 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 243 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 244 245 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 244 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 245 246 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 245 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 246 247 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 246 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 247 248 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 247 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 248 249 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 248 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 249 250 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 249 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 250 251 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 250 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 251 252 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 251 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 252 253 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 252 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 253 254 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 253 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 254 255 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 254 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 255 256 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 255 _ _ (by decide) (by decide +kernel)

theorem positive_transport_240_256 : Transports 240 256 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_240_256
