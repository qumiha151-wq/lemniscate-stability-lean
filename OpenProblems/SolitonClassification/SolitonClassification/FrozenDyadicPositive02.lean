import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [76,76,76,76,76,76,76,76,76,76,76,76,76,76,76,76]
  36708310704331206648180606452061109969649489843938064402500365665961081841112647455162909981534933947623315680322472093106157946881324580528879108707598 120764940037349506436664627229082971590869883726559367945136339388752614982126674260967696006479978838898540885257896590141089327244380464618400775695385 75066907327498675122129241039146831270777638786918233838478377249876901701348307102456928232072161276081254437475998572550063849718109715940451664853346 73056194548252395838220247246547536537063727171183538348974382481245512280265530314875490341381370905615197104557662725350053840122374479131134359591840

private def left : Mark := ⟨18354155352165603324090303226030554984824744921969032201250182832980540920556323727581454990767466973811657840161236046553078973440662290264439554353799,(-60382470018674753218332313614541485795434941863279683972568169694376307491063337130483848003239989419449270442628948295070544663622190232309200387847693),37533453663749337561064620519573415635388819393459116919239188624938450850674153551228464116036080638040627218737999286275031924859054857970225832426673,36528097274126197919110123623273768268531863585591769174487191240622756140132765157437745170690685452807598552278831362675026920061187239565567179795920⟩
private def right : Mark := ⟨(-16410177316730770862897932623062976805180215145101892675582509913564399728163161446707859164642554522043812170311162387295581867211958285842786320503777),(-78519926649760469550279921365250236718163807087183976299059308933010889687882164210023390926806811517106637064056669326644765517173156121987507690855850),36927605755297031080019295292960700469419630836378638641611236579755231269386531132295970449915062201927593043921596632439592837275596045226829537967076,37140462673184322198063657045003450120726613475754890952754388866215998953568598142463808613994588227535126105662898150695132526186004623370240322798703⟩

private theorem cell0 : Transports 32 33 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 32 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 33 34 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 33 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 34 35 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 34 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 35 36 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 35 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 36 37 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 36 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 37 38 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 37 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 38 39 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 38 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 39 40 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 39 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 40 41 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 40 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 41 42 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 41 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 42 43 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 42 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 43 44 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 43 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 44 45 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 44 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 45 46 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 45 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 46 47 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 46 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 47 48 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 47 _ _ (by decide) (by decide +kernel)

theorem positive_transport_32_48 : Transports 32 48 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_32_48
