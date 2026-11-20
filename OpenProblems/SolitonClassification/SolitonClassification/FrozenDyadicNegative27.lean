import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [104,104,104,104,104,104,104,104,104,104,104,104,104,104,104,100]
  414308149233192677773801232010607277165991319929457881167905734227703154516494462626521232486198800502840567302701146999549706378746093516093600296886442 492043803739395358987690558681137788565463975265842611805784716188620366559806609830489828287761923544193723085061843813964017689369958602471355616225550 55647862720078915942908364825513010735883401044817239362014901346630116218373123841986499520519318289272630176413767515515276502889571174892598114288455 88744371721673868420251273330330865631929325187229204830609844527942412616914308459660108902759114082416590621463852025218598567728243620990233327436625

private def left : Mark := ⟨207154074616596338886900616005303638582995659964728940583952867113851577258247231313260616243099400251420283651350573499774853189373046758046800148443221,246021901869697679493845279340568894282731987632921305902892358094310183279903304915244914143880961772096861542530921906982008844684979301235677808112775,(-27823931360039457971454182412756505367941700522408619681007450673315058109186561920993249760259659144636315088206883757757638251444785587446299057144228),(-44372185860836934210125636665165432815964662593614602415304922263971206308457154229830054451379557041208295310731926012609299283864121810495116663718313)⟩
private def right : Mark := ⟨114552852688919534123249856364942223376394561915857849222580654297166109735126871512211251844915564180572991097794939157596915505485086755142238342650224,(-470915997989899556588765326059441823046988563982722741120036951712524111678483701040511620978345391669744114252926158153105001738642511133226383632233491),50193126460609418207920361215331141559943745617270803790656480877996202237742149345969023960985282523834496850505831498321828321011729861303025685646786,(-14957008073345250410166406581164286981877433209585829629909687938346109643266858895048556905420086847298423924104587481356531111518123229201645591346239)⟩

private theorem cell0 : Transports 432 433 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 432 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 433 434 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 433 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 434 435 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 434 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 435 436 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 435 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 436 437 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 436 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 437 438 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 437 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 438 439 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 438 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 439 440 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 439 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 440 441 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 440 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 441 442 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 441 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 442 443 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 442 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 443 444 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 443 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 444 445 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 444 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 445 446 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 445 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 446 447 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 446 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 447 448 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 447 _ _ (by decide) (by decide +kernel)

theorem negative_transport_432_448 : Transports 432 448 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_432_448
