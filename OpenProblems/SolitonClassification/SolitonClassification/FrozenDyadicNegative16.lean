import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [96,96,96,96,96,96,96,96,96,96,96,96,96,96,96,96]
  330892297522587556719583135118836479176238979481586566233670221265661193506655656343433651231733196186816542737708638708054067833127994079905610672512000 234021325463795257279565021865579783664291910497815252975208132021284836569571783059309165178314496620468717695102497602416920925420030324211731817424212 43794669460652877420770763128915840351166714507898158737863810531774635486883900465290977952926953721958471337178304722022452655108433441827933848126609 95153954539049692473398265081327964933716030024844154798406986791772416012828365920865844407687403213233236065527510978602555201630037912077636671676349

private def left : Mark := ⟨165446148761293778359791567559418239588119489740793283116835110632830596753327828171716825615866598093408271368854319354027033916563997039952805336256000,117010662731897628639782510932789891832145955248907626487604066010642418284785891529654582589157248310234358847551248801208460462710015162105865908712106,(-21897334730326438710385381564457920175583357253949079368931905265887317743441950232645488976463476860979235668589152361011226327554216720913966924063305),(-47576977269524846236699132540663982466858015012422077399203493395886208006414182960432922203843701606616618032763755489301277600815018956038818335838175)⟩
private def right : Mark := ⟨117274816834297341029823358738933081700641350371006536824175467657713073143145498155503370007543372654284071323859083502192129363061469087752050612025696,(-262248277142769492106102109599509624048783921868753792703873626286300960299741137647370102322458674349591173468704381652034451663988832232096867613298200),46116605834539624973503914122816471419023896611003677058808853460813861618274292932966909521421735115777963053920064830749457355403008472229206621491862,(-24825807150998135506102875150160145661049942278832976505255691098458919172128921601005128499594344747204015628115211423901387538440476226744938399887434)⟩

private theorem cell0 : Transports 256 257 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 256 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 257 258 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 257 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 258 259 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 258 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 259 260 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 259 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 260 261 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 260 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 261 262 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 261 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 262 263 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 262 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 263 264 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 263 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 264 265 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 264 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 265 266 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 265 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 266 267 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 266 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 267 268 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 267 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 268 269 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 268 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 269 270 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 269 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 270 271 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 270 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 271 272 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 271 _ _ (by decide) (by decide +kernel)

theorem negative_transport_256_272 : Transports 256 272 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_256_272
