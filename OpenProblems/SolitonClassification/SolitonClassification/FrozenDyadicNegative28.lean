import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [100,100,100,100,96,96,96,96,96,96,96,100,100,100,100,100]
  229105705377839068246499712729884446752789123831715698445161308594332219470253743024422503689831128361145982195589878315193831010970173510284476685300448 941831995979799113177530652118883646093977127965445482240073903425048223356967402081023241956690783339488228505852316306210003477285022266452767264466981 100386252921218836415840722430662283119887491234541607581312961755992404475484298691938047921970565047668993701011662996643656642023459722606051371293572 29914016146690500820332813162328573963754866419171659259819375876692219286533717790097113810840173694596847848209174962713062223036246458403291182692477

private def left : Mark := ⟨114552852688919534123249856364942223376394561915857849222580654297166109735126871512211251844915564180572991097794939157596915505485086755142238342650224,(-470915997989899556588765326059441823046988563982722741120036951712524111678483701040511620978345391669744114252926158153105001738642511133226383632233491),50193126460609418207920361215331141559943745617270803790656480877996202237742149345969023960985282523834496850505831498321828321011729861303025685646786,(-14957008073345250410166406581164286981877433209585829629909687938346109643266858895048556905420086847298423924104587481356531111518123229201645591346239)⟩
private def right : Mark := ⟨(-133221076877914872363134881590342286961779013146547956573513111269631398416851674291696026128258082016133233800008368710473963489874359706526166711124669),(-484118667630341305155166788119686176923006391792589195749943665574725920951825525037833223057112975374165371699985349177495396354193872660003644345704609),48804547969558111376487134055338999786910391570015880208592123702744576873906065219328429376540684807859821916118624373044175376361543388479918918497978,(-19004687103026599679346323629705262845856208954162305150765665857588949056394453423041006040720295571972496810440876394788774339688005431875192759271308)⟩

private theorem cell0 : Transports 448 449 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 448 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 449 450 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 449 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 450 451 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 450 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 451 452 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 451 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 452 453 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 452 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 453 454 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 453 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 454 455 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 454 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 455 456 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 455 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 456 457 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 456 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 457 458 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 457 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 458 459 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 458 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 459 460 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 459 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 460 461 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 460 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 461 462 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 461 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 462 463 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 462 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 463 464 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 463 _ _ (by decide) (by decide +kernel)

theorem negative_transport_448_464 : Transports 448 464 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_448_464
