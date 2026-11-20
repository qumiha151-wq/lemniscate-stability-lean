import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [100,100,100,100,100,100,100,100,100,100,100,100,100,100,96,96]
  351625986271586500714832205669845535466846754469236111203332142730292749550725296568743997960511061810772233227616235366463272562803417192611206169158409 330889040676359934801084549371757935613005058900615478950608680014108994183599747834407220614407366805114792869000698381191202701378459602679421582441629 45353300743538534899843106834978470655914187136788085969445299449379688723980717581638693391053446487837931322062476490795839920194509583531649089230682 94421005339137987510838485006752016546889117503973614604589790755966094953994135100168005936385301810678167743326751000594720203083160597100526581164659

private def left : Mark := ⟨(-175812993135793250357416102834922767733423377234618055601666071365146374775362648284371998980255530905386116613808117683231636281401708596305603084579205),(-165444520338179967400542274685878967806502529450307739475304340007054497091799873917203610307203683402557396434500349190595601350689229801339710791220815),22676650371769267449921553417489235327957093568394042984722649724689844361990358790819346695526723243918965661031238245397919960097254791765824544615341,(-47210502669568993755419242503376008273444558751986807302294895377983047476997067550084002968192650905339083871663375500297360101541580298550263290582330)⟩
private def right : Mark := ⟨(-123305547150358752456090860278166378445219229188521325065860232664349319212767932622705834061907249620655119726522352003715659925420912048972729888627836),314002340405822316833418092911747777012686687200456891570466537390406030454022356902537231700753675594701228352534856779399142203742063185167766337612481,(-48480437123321235552451718143599378385782651789313361062080515340341631826198212409492032986019401736357797069062780375784044880363206352764574427182735),(-19816893064467511136538648143922842901790447631543500837047188147786039175963383178657968741125477026165742395991892411569701794245719404237745962339074)⟩

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

theorem negative_transport_304_320 : Transports 304 320 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_304_320
