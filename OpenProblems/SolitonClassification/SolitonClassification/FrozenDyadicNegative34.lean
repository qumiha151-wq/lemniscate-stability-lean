import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [108,108,108,112,112,108,108,108,108,108,108,108,104,104,104,104]
  473331519076527848507414172325042780399676298398959252484781884197112603544399916874918312555288007318173456876034142305498808483566789105776792031210003 539179819763642620017349620712900258299101697462456351847117749038359556330907171763049749790422674719454968159526603784651506230075430258786253136880517 43410896675102663573917744595303104507339701791391135031081677342912044853968715883740133826185274796297409702268282720806998930932423375497121310290496 95329650096131884812575435941468639070648556147345159617435806879917117633446588721799927765049033104024320978872635186076243202952531391533143403551305

private def left : Mark := ⟨(-236665759538263924253707086162521390199838149199479626242390942098556301772199958437459156277644003659086728438017071152749404241783394552888396015605002),(-269589909881821310008674810356450129149550848731228175923558874519179778165453585881524874895211337359727484079763301892325753115037715129393126568440259),21705448337551331786958872297651552253669850895695567515540838671456022426984357941870066913092637398148704851134141360403499465466211687748560655145248,(-47664825048065942406287717970734319535324278073672579808717903439958558816723294360899963882524516552012160489436317593038121601476265695766571701775653)⟩
private def right : Mark := ⟨(-86562875656845936546469953710926617504650581293275205159893910091395032820692741814311165890774052357700463933373527243149275024429706869142941284429969),606678955575761868750423014974660196658159640091337796728469153497811540177895522412902703399642277777950498390904195149723931958095128435177179768651536,(-52170635270302356728111576140027569502679373769148146648356934886618624974465020870491592769617126329925252552687370872437829463690547720359639611244703),(-4613767429111277121700051568890090323888922976418709345302665782345079206672373259312570847047671592540547857669672218705432347595398697736148754873460)⟩

private theorem cell0 : Transports 544 545 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 544 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 545 546 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 545 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 546 547 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 546 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 547 548 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 547 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 548 549 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 548 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 549 550 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 549 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 550 551 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 550 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 551 552 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 551 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 552 553 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 552 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 553 554 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 553 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 554 555 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 554 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 555 556 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 555 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 556 557 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 556 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 557 558 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 557 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 558 559 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 558 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 559 560 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 559 _ _ (by decide) (by decide +kernel)

theorem negative_transport_544_560 : Transports 544 560 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_544_560
