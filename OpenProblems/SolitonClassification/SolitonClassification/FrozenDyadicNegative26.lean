import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [96,96,96,96,96,100,100,100,100,100,100,104,104,104,104,104]
  5314459276086862162216063677087364462169429627111700283035567499653682692249571069016776885942991399993770094112497226157542893862197248104028824705093 912305363525702410665599804619850549063197044290446802850136246841733296215608614046842682864793655185822719657246010748443332930815451852732812176028872 104690329323244499821151409136270053643641005607599294682313114417456354514892691917869129051723318294747799498091879418115092015931961536803997026852185 3490427449180142261749246278942143327155934138046682603616781072408741473360377690799158050962309457452718734869994086996752667147491818845213393920994

private def left : Mark := ⟨(-2657229638043431081108031838543682231084714813555850141517783749826841346124785534508388442971495699996885047056248613078771446931098624052014412352547),456152681762851205332799902309925274531598522145223401425068123420866648107804307023421341432396827592911359828623005374221666465407725926366406088014436,(-52345164661622249910575704568135026821820502803799647341156557208728177257446345958934564525861659147373899749045939709057546007965980768401998513426093),1745213724590071130874623139471071663577967069023341301808390536204370736680188845399579025481154728726359367434997043498376333573745909422606696960497⟩
private def right : Mark := ⟨207154074616596338886900616005303638582995659964728940583952867113851577258247231313260616243099400251420283651350573499774853189373046758046800148443221,246021901869697679493845279340568894282731987632921305902892358094310183279903304915244914143880961772096861542530921906982008844684979301235677808112775,(-27823931360039457971454182412756505367941700522408619681007450673315058109186561920993249760259659144636315088206883757757638251444785587446299057144228),(-44372185860836934210125636665165432815964662593614602415304922263971206308457154229830054451379557041208295310731926012609299283864121810495116663718313)⟩

private theorem cell0 : Transports 416 417 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 416 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 417 418 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 417 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 418 419 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 418 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 419 420 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 419 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 420 421 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 420 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 421 422 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 421 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 422 423 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 422 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 423 424 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 423 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 424 425 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 424 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 425 426 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 425 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 426 427 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 426 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 427 428 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 427 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 428 429 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 428 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 429 430 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 429 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 430 431 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 430 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 431 432 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 431 _ _ (by decide) (by decide +kernel)

theorem negative_transport_416_432 : Transports 416 432 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_416_432
