import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [80,80,80,80,80,80,80,80,80,80,80,80,80,80,80,80]
  173987627822380171907976400572592692355419289345488017862521858242422808353690283609938083118406159887226248195584447130911668915026992841016009851748415 39631883345688753589926327461088157699365161091693428046410450729701173529903139337441981705886051436806169218207830826356199766301342348340787045305047 8444489532076599698700183735212732427449105193626820595027003291651990057364677486320240787739417856811253633747482732074243320228689025840768061251763 104407560713436965617182829551281063901859004684953699807062338287975636818849828819504609577313278569730462589772408140657176460308696562344855026157747

private def left : Mark := ⟨(-86993813911190085953988200286296346177709644672744008931260929121211404176845141804969041559203079943613124097792223565455834457513496420508004925874208),(-19815941672844376794963163730544078849682580545846714023205225364850586764951569668720990852943025718403084609103915413178099883150671174170393522652524),(-4222244766038299849350091867606366213724552596813410297513501645825995028682338743160120393869708928405626816873741366037121660114344512920384030625882),(-52203780356718482808591414775640531950929502342476849903531169143987818409424914409752304788656639284865231294886204070328588230154348281172427513078874)⟩
private def right : Mark := ⟨(-79391719687461012857077453352843603823019360410476685278007111269957728713555520194010058798943442502740271587872670696545052663331348724318042872432551),50858401404762302588745510639941885708812275590614028941501847328257536087652649781183843439135248774662916405503070223970320051896010012003844582341971,(-41141940732295713050992377775515038636360811950885083951290732570751013611178509057259550999294944375308453534817670992998700034806792336830174114834593),(-32409917420090894581623062603781875697926654365434188839114927498016526831910473651770208460570512975952944370259272967910764425146700712490217755504447)⟩

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

theorem negative_transport_64_80 : Transports 64 80 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_64_80
