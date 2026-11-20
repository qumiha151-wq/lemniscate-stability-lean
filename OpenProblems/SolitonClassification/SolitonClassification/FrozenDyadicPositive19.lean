import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [92,92,96,96,96,96,96,96,96,96,100,100,100,100,100,100]
  126878044842774723918442273618691969219808352543216454337639669503152391286363892394101789256622483639886525515792744272765136294286685137681483644791255 642481932047804706348761641677117047718503870687143151947311685285313971462785191787288743385202486549232951890523779185219336337154928601158456957443123 101305340462808676112069451887556281158550508418964865117838365115195960195276284061574015952708957995760946572556267973685668100742721964893462356070150 26635993154034947216480515662003158801145569504566329474753610918020577875717264614308046286319595453058575735111745941875183250779622142838692305359822

private def left : Mark := ⟨(-63439022421387361959221136809345984609904176271608227168819834751576195643181946197050894628311241819943262757896372136382568147143342568840741822395628),(-321240966023902353174380820838558523859251935343571575973655842642656985731392595893644371692601243274616475945261889592609668168577464300579228478721562),50652670231404338056034725943778140579275254209482432558919182557597980097638142030787007976354478997880473286278133986842834050371360982446731178035075,13317996577017473608240257831001579400572784752283164737376805459010288937858632307154023143159797726529287867555872970937591625389811071419346152679911⟩
private def right : Mark := ⟨(-187439587564310323494695880878362761633904795223163758095262163855660077468701146825444924459665785229434141049564506491656518239055457422484227862873535),(-65432788830022275901207715058864651495078878874393954361877124691875277204521600949489209205372079286604293939322111585654814124536934413265027006700155),26582586829483675152660721339688482981065116597972446437485326452138139408286529029346063434287420062956924667907706302898699490899966711157643457489217,(-45126800372392959995224020085134568066036266578292181848313888546877541366279150205220754449186215577136751885940466804987278948664194264525654087686343)⟩

private theorem cell0 : Transports 304 305 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 304 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 305 306 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 305 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 306 307 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 306 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 307 308 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 307 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 308 309 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 308 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 309 310 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 309 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 310 311 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 310 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 311 312 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 311 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 312 313 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 312 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 313 314 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 313 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 314 315 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 314 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 315 316 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 315 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 316 317 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 316 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 317 318 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 317 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 318 319 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 318 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 319 320 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 319 _ _ (by decide) (by decide +kernel)

theorem positive_transport_304_320 : Transports 304 320 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_304_320
