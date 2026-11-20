import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [84,84,88,88,88,88,88,88,88,88,88,92,92,92,92,92]
  15346627015648041297766230534830273270687415864688155974897636824246569883887500286389406582137403181236583122596454269962613874703983728901098336145355 417220610074461178209551038911782246059727726658626077784895635616534047935677023730293574219623762686451577726467840367574315942785113585976267823346811 93525517793022979454919021366038955741714777012550127104994482338928577265502063443914204960701563321828546086057842532702102310956229953025785234590744 47172297581677314828177316024204980258356599552506813101459168872180442525074971927258349782414830774701339296325773855779911641358363801846343852717564

private def left : Mark := ⟨(-7673313507824020648883115267415136635343707932344077987448818412123284941943750143194703291068701590618291561298227134981306937351991864450549168072678),(-208610305037230589104775519455891123029863863329313038892447817808267023967838511865146787109811881343225788863233920183787157971392556792988133911673406),46762758896511489727459510683019477870857388506275063552497241169464288632751031721957102480350781660914273043028921266351051155478114976512892617295372,23586148790838657414088658012102490129178299776253406550729584436090221262537485963629174891207415387350669648162886927889955820679181900923171926358782⟩
private def right : Mark := ⟨(-114114284620257595660751636296742459457015223424450429678520655443809219449046813870567602647795597163895352636096583500878354409095540007248379540006086),(-196653336375163550851605559105610372370930167240075772418838025870586853673911946640953139642184394527741318982099642887403200288245252858844058513357132),52019731640245546273527454959540070861801734773016271860513361121032818214314782350679065695067624041443996052161481874174071419438567351717375130795019,(-6083547852501922214144147113152925695236734115892238572941067138442863787160862864281923151695121752230830707437107235986198491141388779424064271967394)⟩

private theorem cell0 : Transports 192 193 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 192 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 193 194 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 193 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 194 195 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 194 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 195 196 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 195 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 196 197 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 196 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 197 198 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 197 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 198 199 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 198 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 199 200 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 199 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 200 201 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 200 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 201 202 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 201 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 202 203 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 202 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 203 204 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 203 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 204 205 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 204 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 205 206 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 205 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 206 207 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 206 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 207 208 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 207 _ _ (by decide) (by decide +kernel)

theorem positive_transport_192_208 : Transports 192 208 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_192_208
