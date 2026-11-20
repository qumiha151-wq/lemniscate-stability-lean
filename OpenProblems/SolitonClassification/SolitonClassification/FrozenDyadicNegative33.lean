import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [100,96,100,100,100,100,100,104,104,104,104,108,108,108,108,108]
  51815423693353104818684119465990115964342976024954760855323739795565301201795804599020789184663580167127274205198832093068774358123508399142864815733542 1155239957520851495678174524499369110629249896698045832028397479644760301803542343891446863865792636633855709497844757629968853515470819514771134719510073 104662387550136794518209248596491421270737861098798006026513599988778855777529098683503649111907220538446055543015073460309438808483985288443657007843840 4246500899840700875957025727078990401523346682002235969840343999459473230659613657203190414092780761157042762231488680467581850735415287749350183982539

private def left : Mark := ⟨25907711846676552409342059732995057982171488012477380427661869897782650600897902299510394592331790083563637102599416046534387179061754199571432407866771,(-577619978760425747839087262249684555314624948349022916014198739822380150901771171945723431932896318316927854748922378814984426757735409757385567359755037),52331193775068397259104624298245710635368930549399003013256799994389427888764549341751824555953610269223027771507536730154719404241992644221828503921920,(-2123250449920350437978512863539495200761673341001117984920171999729736615329806828601595207046390380578521381115744340233790925367707643874675091991270)⟩
private def right : Mark := ⟨(-236665759538263924253707086162521390199838149199479626242390942098556301772199958437459156277644003659086728438017071152749404241783394552888396015605002),(-269589909881821310008674810356450129149550848731228175923558874519179778165453585881524874895211337359727484079763301892325753115037715129393126568440259),21705448337551331786958872297651552253669850895695567515540838671456022426984357941870066913092637398148704851134141360403499465466211687748560655145248,(-47664825048065942406287717970734319535324278073672579808717903439958558816723294360899963882524516552012160489436317593038121601476265695766571701775653)⟩

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

theorem negative_transport_528_544 : Transports 528 544 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_528_544
