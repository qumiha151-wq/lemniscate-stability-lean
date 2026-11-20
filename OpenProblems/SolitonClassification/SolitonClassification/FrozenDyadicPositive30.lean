import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [104,104,104,104,108,108,108,108,108,108,108,108,108,108,104,104]
  323528687537153814805522382128470813023981932580102446731741660406113483931727854664486307265498964265324948407486168146333206162293943772718154069901335 883505575959682573046091939453653293577336446491050803344835627151089098302450741656680931244513915477759390888339799336513631233438323496779337318217877 102193097104522316090100299514782565841565984053081577258036215878736428879994947973376228697943628747948567704989520845801489673814256642721063146861012 22996065789022477526262136669214595581827729867482175628219583549883198514614521668902484906598388153873874544883446994162874686640313266469434751009991

private def left : Mark := ⟨(-161764343768576907402761191064235406511990966290051223365870830203056741965863927332243153632749482132662474203743084073166603081146971886359077034950668),(-441752787979841286523045969726826646788668223245525401672417813575544549151225370828340465622256957738879695444169899668256815616719161748389668659108939),51096548552261158045050149757391282920782992026540788629018107939368214439997473986688114348971814373974283852494760422900744836907128321360531573430506,(-11498032894511238763131068334607297790913864933741087814109791774941599257307260834451242453299194076936937272441723497081437343320156633234717375504996)⟩
private def right : Mark := ⟨(-178875383703691119776261444948350207131321832746044041659797786204597530786060007350380594679617964444013970568264429664243484716707125404341076768220640),414876174397025897447471759444268022146885907629363936269101419530962303273357389468024231930465665864056663173785833834432254659937895337402939454482818,(-31892173027009105231756148328531163861654861095994981940908715955643567258070451806804480002358020807450228031889013886619537625076485628674097414053878),(-41544570451650564967425335876200906351023987965880892752238880128633784751917671902106984630510069223570130425737514768992484660622921694943811668059789)⟩

private theorem cell0 : Transports 480 481 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 480 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 481 482 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 481 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 482 483 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 482 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 483 484 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 483 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 484 485 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 484 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 485 486 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 485 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 486 487 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 486 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 487 488 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 487 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 488 489 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 488 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 489 490 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 489 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 490 491 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 490 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 491 492 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 491 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 492 493 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 492 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 493 494 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 493 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 494 495 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 494 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 495 496 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 495 _ _ (by decide) (by decide +kernel)

theorem positive_transport_480_496 : Transports 480 496 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_480_496
