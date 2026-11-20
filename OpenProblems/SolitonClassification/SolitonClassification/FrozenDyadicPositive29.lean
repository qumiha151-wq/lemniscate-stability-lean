import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [100,100,96,96,96,96,96,96,96,100,100,100,100,100,104,104]
  162382129153089647318431457196410469171273074447512726849976635002246477840236991759140022938816242427422155749331373059258859394005216165113544075956084 956588188703789213223903783172867483944018155351710283934239929015713601355473549196028951261877829341633858184663423334983833220703241940819536452467661 103254778016609797453354428882789955059660591247081165540876629467496120956240513569802565017855091847851005016706361413108166392543778639185376613349096 17626654655039097035024760435356753208475248567156585490458633996688123825329219118317670434973952799007414255092761159955591901834964130222112041156380

private def left : Mark := ⟨81191064576544823659215728598205234585636537223756363424988317501123238920118495879570011469408121213711077874665686529629429697002608082556772037978042,(-478294094351894606611951891586433741972009077675855141967119964507856800677736774598014475630938914670816929092331711667491916610351620970409768226233831),51627389008304898726677214441394977529830295623540582770438314733748060478120256784901282508927545923925502508353180706554083196271889319592688306674548,8813327327519548517512380217678376604237624283578292745229316998344061912664609559158835217486976399503707127546380579977795950917482065111056020578190⟩
private def right : Mark := ⟨(-161764343768576907402761191064235406511990966290051223365870830203056741965863927332243153632749482132662474203743084073166603081146971886359077034950668),(-441752787979841286523045969726826646788668223245525401672417813575544549151225370828340465622256957738879695444169899668256815616719161748389668659108939),51096548552261158045050149757391282920782992026540788629018107939368214439997473986688114348971814373974283852494760422900744836907128321360531573430506,(-11498032894511238763131068334607297790913864933741087814109791774941599257307260834451242453299194076936937272441723497081437343320156633234717375504996)⟩

private theorem cell0 : Transports 464 465 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 464 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 465 466 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 465 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 466 467 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 466 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 467 468 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 467 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 468 469 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 468 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 469 470 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 469 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 470 471 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 470 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 471 472 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 471 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 472 473 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 472 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 473 474 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 473 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 474 475 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 474 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 475 476 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 475 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 476 477 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 476 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 477 478 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 477 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 478 479 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 478 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 479 480 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 479 _ _ (by decide) (by decide +kernel)

theorem positive_transport_464_480 : Transports 464 480 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_464_480
