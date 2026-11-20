import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [104,100,100,100,100,100,100,100,96,96,96,96,96,92,96,96]
  357408883804935801453371964781964441760122893436347170337953188711893126063150376952107714086014153346162399128667019825708915401134887443428622287134361 612910022168857096803854299660824537818792620086960953393167576162782238221792688358487675570260472938577788713434754340336818484386400716787704586118000 48781917021817690822905542374409139476229658129209032019602042289151349515173213167004544577125449490840659610643723144634931018810431078482217831211995 92696131037189846677330558919176183696637930499904334141346844921103793897114161070599529724855347774809317822451704716175455267174432656029659179375029

private def left : Mark := ⟨(-178704441902467900726685982390982220880061446718173585168976594355946563031575188476053857043007076673081199564333509912854457700567443721714311143567181),306455011084428548401927149830412268909396310043480476696583788081391119110896344179243837785130236469288894356717377170168409242193200358393852293059000,(-24390958510908845411452771187204569738114829064604516009801021144575674757586606583502272288562724745420329805321861572317465509405215539241108915605998),(-46348065518594923338665279459588091848318965249952167070673422460551896948557080535299764862427673887404658911225852358087727633587216328014829589687515)⟩
private def right : Mark := ⟨30654005247441855497103732260919185150088122399210567449027067072263141066222169234812367961287480900650802228034863352226980850397643811610306343484339,453190042999275394789965067068256178117505663177712477068606067446239658526197734088998759180336099647868475539655855122856730245436843961116390507358814,(-49504309338483063566056934209803921743720903677729853833832262476394881664849655745017194675019930622704374264038583020768804159702597264478238721395777),(-17099280432714789737744682270834401526948518809646085624576786947149377560284365135638071024111622287590037066429482811177316923793317592168860114938493)⟩

private theorem cell0 : Transports 416 417 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 416 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 417 418 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 417 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 418 419 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 418 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 419 420 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 419 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 420 421 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 420 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 421 422 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 421 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 422 423 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 422 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 423 424 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 423 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 424 425 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 424 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 425 426 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 425 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 426 427 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 426 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 427 428 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 427 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 428 429 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 428 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 429 430 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 429 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 430 431 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 430 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 431 432 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 431 _ _ (by decide) (by decide +kernel)

theorem positive_transport_416_432 : Transports 416 432 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_416_432
