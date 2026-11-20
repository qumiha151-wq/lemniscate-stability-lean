import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [92,92,92,92,92,92,92,92,96,96,96,96,96,96,96,96]
  102452632335336427315295832061582520281130867973457658491232486557085231018623919587935127628340245411577233148478754466292772829774698656324392718172726 532879635193638672371010413653869661636518945722738308894899029412107737570709997176934730935493058221008142349145265674425742527921512151943508073437002 104618818044816664118540720182373422629829788359988665758051694337005037901871814718110316449417150174358687422776873360943059465286929932827972182457835 5210666799260965116144913200309099663006482323334710460900741609152422656947398223786710765507051322624054496670595873695964115567632591011083917862309

private def left : Mark := ⟨51226316167668213657647916030791260140565433986728829245616243278542615509311959793967563814170122705788616574239377233146386414887349328162196359086363,266439817596819336185505206826934830818259472861369154447449514706053868785354998588467365467746529110504071174572632837212871263960756075971754036718501,(-52309409022408332059270360091186711314914894179994332879025847168502518950935907359055158224708575087179343711388436680471529732643464966413986091228918),(-2605333399630482558072456600154549831503241161667355230450370804576211328473699111893355382753525661312027248335297936847982057783816295505541958931155)⟩
private def right : Mark := ⟨165446148761293778359791567559418239588119489740793283116835110632830596753327828171716825615866598093408271368854319354027033916563997039952805336256000,117010662731897628639782510932789891832145955248907626487604066010642418284785891529654582589157248310234358847551248801208460462710015162105865908712106,(-21897334730326438710385381564457920175583357253949079368931905265887317743441950232645488976463476860979235668589152361011226327554216720913966924063305),(-47576977269524846236699132540663982466858015012422077399203493395886208006414182960432922203843701606616618032763755489301277600815018956038818335838175)⟩

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

theorem negative_transport_240_256 : Transports 240 256 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_240_256
