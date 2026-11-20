import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [92,92,92,92,92,92,92,92,92,92,92,88,88,88,88,88]
  268086742294618892790230797507134829993672298396043613908869922332827887449968755061879738488537179545283674374228891973282919102786133063076342705110406 30222749361321821908390709551331754545874094831587053015314693328505418723862547175012685288278675344096556286536083555321680372449208037635853175756786 49708117264282438816966581569374432527700367625197608532219497006638720318750937927946900318995696588810715989786088833182073833246908532021553852860522 92202772277343827798522333872528845941678185220293768947789460883845304658832643107176268879124791154195831635475362379055314750175775160864588090747689

private def left : Mark := ⟨134043371147309446395115398753567414996836149198021806954434961166413943724984377530939869244268589772641837187114445986641459551393066531538171352555203,15111374680660910954195354775665877272937047415793526507657346664252709361931273587506342644139337672048278143268041777660840186224604018817926587878393,24854058632141219408483290784687216263850183812598804266109748503319360159375468963973450159497848294405357994893044416591036916623454266010776926430261,(-46101386138671913899261166936264422970839092610146884473894730441922652329416321553588134439562395577097915817737681189527657375087887580432294045373845)⟩
private def right : Mark := ⟨89127061751212205244906368352464866996635408270544149122630237091163425813843802562785036353115583062143930684216905842708945048325761051522053133740847,(-168256781533072691770142510203672567976412660243488065709353579213090404022268238216019723343903486227845704441436549982558667764061724783768315294610043),52268172065574978265905706976804449109870957198369006603140402225360846420939245579858603912794349150314434654122093789450800298619285107497636163139228,3331699764428339291749041943431372530942172885876084178242972880168866637497973301537098882705285320565261947707989186481039451174734507027221674355402⟩

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

theorem positive_transport_160_176 : Transports 160 176 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_160_176
