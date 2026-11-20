import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [84,84,84,84,84,84,84,84,84,84,84,84,88,88,88,88]
  7795614680464120893233656633549807921575754155192889708893538033459383483474459477428265252874414446808305565780143033642242020424392362089249427290644 298707705341570032528293545536484815613942336159316810974654180987299717387517451653576809443177255451961354401815521248338835639812172361103646333319164 88355194273801697385150853913874775375318728327168614998302016513011794360947891296590533961876365872313300140103836255435198028131509569874973284286327 56263734167100365962498844041630104192100192070036665678077281115997446838310572645143728828934960129355206544263264669858922770241329656045864734071059

private def left : Mark := ⟨3897807340232060446616828316774903960787877077596444854446769016729691741737229738714132626437207223404152782890071516821121010212196181044624713645322,149353852670785016264146772768242407806971168079658405487327090493649858693758725826788404721588627725980677200907760624169417819906086180551823166659582,(-44177597136900848692575426956937387687659364163584307499151008256505897180473945648295266980938182936156650070051918127717599014065754784937486642143164),(-28131867083550182981249422020815052096050096035018332839038640557998723419155286322571864414467480064677603272131632334929461385120664828022932367035530)⟩
private def right : Mark := ⟨82436385249110761515106488806074903424769805811738669978035775213859366007903606859394854502599956170637286612219536941566100230896978592268717743334218,155857879258357493068598653693781947306002054592582242429244788663003716936089814753530581102002582549928180530384236424949939308396864758606822016185236,(-29371004409442024563879650571571161379091624610369656597208936603461450345763273008463382404495833916851191774811447625698543275612325114377450535305410),(-43363649919920042306226321786518865667980090425739135994247866446542456395809024633083882766350893694405649556204879357576904660877315518313055145907495)⟩

private theorem cell0 : Transports 128 129 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 128 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 129 130 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 129 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 130 131 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 130 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 131 132 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 131 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 132 133 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 132 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 133 134 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 133 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 134 135 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 134 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 135 136 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 135 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 136 137 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 136 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 137 138 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 137 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 138 139 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 138 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 139 140 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 139 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 140 141 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 140 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 141 142 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 141 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 142 143 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 142 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 143 144 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 143 _ _ (by decide) (by decide +kernel)

theorem positive_transport_128_144 : Transports 128 144 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_128_144
