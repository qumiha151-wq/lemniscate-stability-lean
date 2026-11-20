import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [88,88,88,88,88,88,88,88,84,84,84,84,84,84,84,84]
  178254123502424410489812736704929733993270816541088298245260474182326851627687605125570072706231166124287861368433811685417890096651522103044106267481694 336513563066145383540285020407345135952825320486976131418707158426180808044536476432039446687806972455691408882873099965117335528123449567536630589220085 104536344131149956531811413953608898219741914396738013206280804450721692841878491159717207825588698300628869308244187578901600597238570214995272326278456 6663399528856678583498083886862745061884345771752168356485945760337733274995946603074197765410570641130523895415978372962078902349469014054443348710804

private def left : Mark := ⟨89127061751212205244906368352464866996635408270544149122630237091163425813843802562785036353115583062143930684216905842708945048325761051522053133740847,(-168256781533072691770142510203672567976412660243488065709353579213090404022268238216019723343903486227845704441436549982558667764061724783768315294610043),52268172065574978265905706976804449109870957198369006603140402225360846420939245579858603912794349150314434654122093789450800298619285107497636163139228,3331699764428339291749041943431372530942172885876084178242972880168866637497973301537098882705285320565261947707989186481039451174734507027221674355402⟩
private def right : Mark := ⟨(-7673313507824020648883115267415136635343707932344077987448818412123284941943750143194703291068701590618291561298227134981306937351991864450549168072678),(-208610305037230589104775519455891123029863863329313038892447817808267023967838511865146787109811881343225788863233920183787157971392556792988133911673406),46762758896511489727459510683019477870857388506275063552497241169464288632751031721957102480350781660914273043028921266351051155478114976512892617295372,23586148790838657414088658012102490129178299776253406550729584436090221262537485963629174891207415387350669648162886927889955820679181900923171926358782⟩

private theorem cell0 : Transports 176 177 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 176 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 177 178 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 177 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 178 179 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 178 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 179 180 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 179 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 180 181 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 180 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 181 182 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 181 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 182 183 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 182 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 183 184 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 183 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 184 185 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 184 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 185 186 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 185 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 186 187 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 186 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 187 188 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 187 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 188 189 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 188 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 189 190 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 189 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 190 191 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 190 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 191 192 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 191 _ _ (by decide) (by decide +kernel)

theorem positive_transport_176_192 : Transports 176 192 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_176_192
