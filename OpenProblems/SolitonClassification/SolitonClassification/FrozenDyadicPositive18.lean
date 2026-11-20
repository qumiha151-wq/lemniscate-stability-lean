import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [92,92,92,92,92,92,92,88,88,88,88,92,92,92,92,92]
  182809817859397587307523035799813363032054414661977446608831909732223039230682893076225039320522990309812044917209190734119257621726757890253113791805780 575837834257555102000035117347125868093390691098389076328498029411475804604229270428759887063548556118941567235484468776182686971673065811486083446204319 104096043334016337729713485237139609313805562916601589822817563451782916921985270665682712157660376314652981112489841051479505738591056774834136458898312 11673127249797722688894830733705500260914478699182153766121849082583925115828675999714162331479818234327371194479350182107371586081610083754258101699788

private def left : Mark := ⟨91404908929698793653761517899906681516027207330988723304415954866111519615341446538112519660261495154906022458604595367059628810863378945126556895902890,(-287918917128777551000017558673562934046695345549194538164249014705737902302114635214379943531774278059470783617742234388091343485836532905743041723102160),52048021667008168864856742618569804656902781458300794911408781725891458460992635332841356078830188157326490556244920525739752869295528387417068229449156,5836563624898861344447415366852750130457239349591076883060924541291962557914337999857081165739909117163685597239675091053685793040805041877129050849894⟩
private def right : Mark := ⟨(-63439022421387361959221136809345984609904176271608227168819834751576195643181946197050894628311241819943262757896372136382568147143342568840741822395628),(-321240966023902353174380820838558523859251935343571575973655842642656985731392595893644371692601243274616475945261889592609668168577464300579228478721562),50652670231404338056034725943778140579275254209482432558919182557597980097638142030787007976354478997880473286278133986842834050371360982446731178035075,13317996577017473608240257831001579400572784752283164737376805459010288937858632307154023143159797726529287867555872970937591625389811071419346152679911⟩

private theorem cell0 : Transports 288 289 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 288 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 289 290 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 289 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 290 291 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 290 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 291 292 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 291 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 292 293 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 292 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 293 294 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 293 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 294 295 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 294 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 295 296 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 295 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 296 297 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 296 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 297 298 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 297 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 298 299 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 298 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 299 300 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 299 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 300 301 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 300 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 301 302 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 301 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 302 303 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 302 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 303 304 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 303 _ _ (by decide) (by decide +kernel)

theorem positive_transport_288_304 : Transports 288 304 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_288_304
