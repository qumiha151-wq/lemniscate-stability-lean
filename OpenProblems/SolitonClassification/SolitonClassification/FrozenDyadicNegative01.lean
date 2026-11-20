import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [72,72,72,72,76,76,76,76,76,76,76,76,76,76,76,76]
  39128209179742091888084406180793847852161231715535363845320333503178904608482756640802266042304372558208931987910703248867011185131401876954064886317679 51530521410676566017530066370581205830581394513699849354947866991555013369137075544113329659705018178472031500412646448681002784411868716597369247387603 103639781156030385369442864044222535549930488278591040856905015289239193419313091724411380328079084816907407142062907287967871919341105459597099722272406 15200128273060935063664991600153094415823500916141931178166490160872291877674008432642816877726647415865938680818600619347348489323815299129982733253893

private def left : Mark := ⟨(-19564104589871045944042203090396923926080615857767681922660166751589452304241378320401133021152186279104465993955351624433505592565700938477032443158840),(-25765260705338283008765033185290602915290697256849924677473933495777506684568537772056664829852509089236015750206323224340501392205934358298684623693802),51819890578015192684721432022111267774965244139295520428452507644619596709656545862205690164039542408453703571031453643983935959670552729798549861136203,(-7600064136530467531832495800076547207911750458070965589083245080436145938837004216321408438863323707932969340409300309673674244661907649564991366626947)⟩
private def right : Mark := ⟨(-38442156955612125685953273197385720810099592394390992786286360926667984969088262730215289383097222255376153127888375023974117375985256384470705601634671),(-48725060333817911723202251701325787323716534241584833499182023422031101122766942444883168095600881338613120877166457405278863997394088670421904187655128),47964332854737560561138495383541570807351432972147919778490074340395080268371602709821705056214301214059238984681195716870319977685758216506897273821497,(-21035322868850560046127860985545203725357860197901057688025121957473047358774034182430899742959912286317294681974047991840483111172557910730908126435620)⟩

private theorem cell0 : Transports 16 17 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 16 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 17 18 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 17 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 18 19 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 18 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 19 20 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 19 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 20 21 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 20 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 21 22 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 21 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 22 23 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 22 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 23 24 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 23 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 24 25 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 24 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 25 26 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 25 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 26 27 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 26 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 27 28 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 27 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 28 29 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 28 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 29 30 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 29 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 30 31 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 30 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 31 32 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 31 _ _ (by decide) (by decide +kernel)

theorem negative_transport_16_32 : Transports 16 32 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_16_32
