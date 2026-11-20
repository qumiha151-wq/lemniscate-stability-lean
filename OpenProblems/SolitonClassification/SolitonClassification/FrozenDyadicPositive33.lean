import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [108,108,108,108,108,104,104,104,104,104,104,100,100,100,100,96]
  468889918178659864554955967005093804664610289077422068198580541158409492900778443613191980535005168048396655290602892543372430180384075630696750209380452 317535416035751633301660173245684786344970056219267303707661562878848198579933564056634569619592674186364995313217267815116373520870625681263768299600761 57988226630238533048838460584201493794472229507482967185135264086287521095570519077474762938382505342499615503453929010060706753688813085844675152105228 87233099852449769473119527189733388818691164746715650029157079454994156393777096367982312189157842378127595531759178244033714509899362368259141478309393

private def left : Mark := ⟨234444959089329932277477983502546902332305144538711034099290270579204746450389221806595990267502584024198327645301446271686215090192037815348375104690226,(-158767708017875816650830086622842393172485028109633651853830781439424099289966782028317284809796337093182497656608633907558186760435312840631884149800381),28994113315119266524419230292100746897236114753741483592567632043143760547785259538737381469191252671249807751726964505030353376844406542922337576052614,(-43616549926224884736559763594866694409345582373357825014578539727497078196888548183991156094578921189063797765879589122016857254949681184129570739154697)⟩
private def right : Mark := ⟨(-317169628852647245056179568588366751547723996333094112567683466965523598009393588366483161568994136512184294225059182145459127501115523843681343169356),(-569007806419988102825652839556263034057464332675484383044295575535833982510143811379417223176715299826812313645885823721752282947630927672284997656061429),50373991009985641663915657866642349704708323095844578873939523086691077908892351551431135341279021424310096233472159834308521829920265393207835596122918,14336075617920341275003171247027053659382176958506190214244952379744748033042349885497670002129737097101499789332385996319918973355977600197008101973257⟩

private theorem cell0 : Transports 528 529 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 528 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 529 530 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 529 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 530 531 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 530 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 531 532 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 531 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 532 533 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 532 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 533 534 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 533 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 534 535 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 534 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 535 536 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 535 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 536 537 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 536 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 537 538 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 537 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 538 539 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 538 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 539 540 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 539 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 540 541 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 540 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 541 542 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 541 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 542 543 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 542 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 543 544 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 543 _ _ (by decide) (by decide +kernel)

theorem positive_transport_528_544 : Transports 528 544 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_528_544
