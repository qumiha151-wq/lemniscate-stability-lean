import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [88,88,88,88,88,88,88,88,88,92,92,92,92,92,92,92]
  164872770498221523030212977612149806849539611623477339956071550427718732015807213718789709005199912341274573224439073883132200461793957184537435486668436 311715758516714986137197307387563894612004109185164484858489577326007433872179629507061162204005165099856361060768472849899878616793729517213644032370472 58742008818884049127759301143142322758183249220739313194417873206922900691526546016926764808991667833702383549622895251397086551224650228754901070610819 86727299839840084612452643573037731335960180851478271988495732893084912791618049266167765532701787388811299112409758715153809321754631036626110291814989

private def left : Mark := ⟨82436385249110761515106488806074903424769805811738669978035775213859366007903606859394854502599956170637286612219536941566100230896978592268717743334218,155857879258357493068598653693781947306002054592582242429244788663003716936089814753530581102002582549928180530384236424949939308396864758606822016185236,(-29371004409442024563879650571571161379091624610369656597208936603461450345763273008463382404495833916851191774811447625698543275612325114377450535305410),(-43363649919920042306226321786518865667980090425739135994247866446542456395809024633083882766350893694405649556204879357576904660877315518313055145907495)⟩
private def right : Mark := ⟨134043371147309446395115398753567414996836149198021806954434961166413943724984377530939869244268589772641837187114445986641459551393066531538171352555203,15111374680660910954195354775665877272937047415793526507657346664252709361931273587506342644139337672048278143268041777660840186224604018817926587878393,24854058632141219408483290784687216263850183812598804266109748503319360159375468963973450159497848294405357994893044416591036916623454266010776926430261,(-46101386138671913899261166936264422970839092610146884473894730441922652329416321553588134439562395577097915817737681189527657375087887580432294045373845)⟩

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

theorem positive_transport_144_160 : Transports 144 160 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_144_160
