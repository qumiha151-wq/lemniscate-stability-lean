import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [104,104,104,104,104,104,104,104,104,104,104,104,100,100,100,100]
  435755746238369568335964815991746904361771306535585113893003482273465400876872633710827081307096963447690346299348754337727756222845695876530999397901544 235860442572861973099474095987253379196801587287741914908328164019782324619957783886947079756326199360797722198991204646551250774448158483244087895786540 7235505785650254620567136243294530509913123880834849507546519356655097274934047072159370493509477439953477263622066870436857617643993167259898669865268 104498304261902733797266866227237219647818110397433380467548555023261778537017961562698006890876088942074133871911464236535465821566129309586741260887355

private def left : Mark := ⟨217877873119184784167982407995873452180885653267792556946501741136732700438436316855413540653548481723845173149674377168863878111422847938265499698950772,117930221286430986549737047993626689598400793643870957454164082009891162309978891943473539878163099680398861099495602323275625387224079241622043947893270,3617752892825127310283568121647265254956561940417424753773259678327548637467023536079685246754738719976738631811033435218428808821996583629949334932634,(-52249152130951366898633433113618609823909055198716690233774277511630889268508980781349003445438044471037066935955732118267732910783064654793370630443678)⟩
private def right : Mark := ⟨81191064576544823659215728598205234585636537223756363424988317501123238920118495879570011469408121213711077874665686529629429697002608082556772037978042,(-478294094351894606611951891586433741972009077675855141967119964507856800677736774598014475630938914670816929092331711667491916610351620970409768226233831),51627389008304898726677214441394977529830295623540582770438314733748060478120256784901282508927545923925502508353180706554083196271889319592688306674548,8813327327519548517512380217678376604237624283578292745229316998344061912664609559158835217486976399503707127546380579977795950917482065111056020578190⟩

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

theorem positive_transport_448_464 : Transports 448 464 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_448_464
