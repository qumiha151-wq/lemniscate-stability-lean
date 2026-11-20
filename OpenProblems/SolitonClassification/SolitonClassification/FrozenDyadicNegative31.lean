import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [100,100,100,100,104,104,104,104,104,108,108,108,108,108,108,108]
  96938093641555351099795902111108123634414076833782041015402216424468133669524694982072675652374386796918397263048273914272827395515629978351580177175162 1089232306673649234262169358326347981329352234963760505258431910800542049091568494966340319788377591415631686273951867723466293585035852460301381324578666 104742661039800213932800789496892725337740291610347991315126986236049849704208153645212571365528612732783948504584269265812219966233597029029549511909275 1105936656818885602379902505525049854383942591574249886622979669415460987234180125648751421788031652428102459148029946444982785618984852348953492156005

private def left : Mark := ⟨48469046820777675549897951055554061817207038416891020507701108212234066834762347491036337826187193398459198631524136957136413697757814989175790088587581,544616153336824617131084679163173990664676117481880252629215955400271024545784247483170159894188795707815843136975933861733146792517926230150690662289333,(-52371330519900106966400394748446362668870145805173995657563493118024924852104076822606285682764306366391974252292134632906109983116798514514774755954638),(-552968328409442801189951252762524927191971295787124943311489834707730493617090062824375710894015826214051229574014973222491392809492426174476746078003)⟩
private def right : Mark := ⟨242081339975386239041202021084538079801533052377284776805402582967198485135835952067746099739180299314384103847980837381301910853928737624365146453847362,(-37220717599511200721624632775078408619422659706281547569487918564736098655803973235228788828328959380431014586943163730676446207969683910211079161979468),2606611630551329517176138779106294031201437771076777773161896885760301376718194613193432343305352655035524162689977416006779100436206976081111865809040,(-52309345342914767555149650007609108405998032766337210578080003771727721124752421020861685781803409927344816789106897642066667098855502630544265389582896)⟩

private theorem cell0 : Transports 496 497 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 496 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 497 498 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 497 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 498 499 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 498 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 499 500 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 499 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 500 501 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 500 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 501 502 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 501 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 502 503 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 502 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 503 504 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 503 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 504 505 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 504 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 505 506 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 505 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 506 507 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 506 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 507 508 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 507 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 508 509 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 508 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 509 510 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 509 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 510 511 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 510 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 511 512 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 511 _ _ (by decide) (by decide +kernel)

theorem negative_transport_496_512 : Transports 496 512 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_496_512
