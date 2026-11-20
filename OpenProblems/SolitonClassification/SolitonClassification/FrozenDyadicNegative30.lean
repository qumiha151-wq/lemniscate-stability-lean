import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [108,104,104,104,104,104,100,100,100,100,100,96,96,96,96,100]
  404786267749154905218666279208425204584025325968952197235075116032446270014447465235031446097584065946701462218738769152280151537340278928712753423440663 690003432116596671512386770312751123971042011100742098147754674638586484589628607608016565653384695580358840824686804176637673156176459460645732169494782 72414984402923724077026711539189252261133661029150024137610888164049389160274106070943984026652718151836372585562649392496877023727502375847760612568729 75685653670373298425841537421669979822677140744172109979021953722754833731658548711652433741213789600338086334507181374850926572775164453204574659843591

private def left : Mark := ⟨(-202393133874577452609333139604212602292012662984476098617537558016223135007223732617515723048792032973350731109369384576140075768670139464356376711720332),345001716058298335756193385156375561985521005550371049073877337319293242294814303804008282826692347790179420412343402088318836578088229730322866084747391,(-36207492201461862038513355769594626130566830514575012068805444082024694580137053035471992013326359075918186292781324696248438511863751187923880306284365),(-37842826835186649212920768710834989911338570372086054989510976861377416865829274355826216870606894800169043167253590687425463286387582226602287329921796)⟩
private def right : Mark := ⟨48469046820777675549897951055554061817207038416891020507701108212234066834762347491036337826187193398459198631524136957136413697757814989175790088587581,544616153336824617131084679163173990664676117481880252629215955400271024545784247483170159894188795707815843136975933861733146792517926230150690662289333,(-52371330519900106966400394748446362668870145805173995657563493118024924852104076822606285682764306366391974252292134632906109983116798514514774755954638),(-552968328409442801189951252762524927191971295787124943311489834707730493617090062824375710894015826214051229574014973222491392809492426174476746078003)⟩

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

theorem negative_transport_480_496 : Transports 480 496 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_480_496
