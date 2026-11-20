import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [100,100,100,104,104,104,104,104,104,104,104,104,104,104,104,104]
  297670825017373982553235312911573387504804827046704242507248788080638955629605700133288763129111828264773657511492721075886025594778187114026295591185807 737082774435231388930653394134186385481167657835051121588522121522245869501348225237118557196324996646372198681974673673969469830890705720855727467851393 102680886231444656347208987895029398307557028624423418036034070625767987084495244922637393896468642664069654884024814658656729968996051950073047699801658 20709508451735317939145658812028561877684518478894254000337493181696348442031218048149749161835482950639440531384483739393646424936138809518611355953567

private def left : Mark := ⟨(-148835412508686991276617656455786693752402413523352121253624394040319477814802850066644381564555914132386828755746360537943012797389093557013147795592904),(-368541387217615694465326697067093192740583828917525560794261060761122934750674112618559278598162498323186099340987336836984734915445352860427863733925697),51340443115722328173604493947514699153778514312211709018017035312883993542247622461318696948234321332034827442012407329328364984498025975036523849900829,(-10354754225867658969572829406014280938842259239447127000168746590848174221015609024074874580917741475319720265692241869696823212468069404759305677976784)⟩
private def right : Mark := ⟨(-178704441902467900726685982390982220880061446718173585168976594355946563031575188476053857043007076673081199564333509912854457700567443721714311143567181),306455011084428548401927149830412268909396310043480476696583788081391119110896344179243837785130236469288894356717377170168409242193200358393852293059000,(-24390958510908845411452771187204569738114829064604516009801021144575674757586606583502272288562724745420329805321861572317465509405215539241108915605998),(-46348065518594923338665279459588091848318965249952167070673422460551896948557080535299764862427673887404658911225852358087727633587216328014829589687515)⟩

private theorem cell0 : Transports 400 401 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 400 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 401 402 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 401 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 402 403 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 402 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 403 404 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 403 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 404 405 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 404 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 405 406 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 405 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 406 407 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 406 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 407 408 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 407 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 408 409 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 408 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 409 410 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 409 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 410 411 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 410 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 411 412 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 411 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 412 413 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 412 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 413 414 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 413 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 414 415 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 414 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 415 416 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 415 _ _ (by decide) (by decide +kernel)

theorem positive_transport_400_416 : Transports 400 416 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_400_416
