import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [104,104,104,104,100,100,100,100,100,100,100,96,96,96,96,96]
  399559282370830669746097449120653402856962650260365927717463294637071558384212964099872075360791014772253178159125787424484069778480530090563381523391877 418758241512799319325329274061850268245873620643381164683111040697174759070524270452745794001937579590261003880052175367846503667216294715623452441123818 54938567673925581210617045783209194226935409918049025185474952684785476845324553330208312625266269761364599615325456584362877072723103375941731047361961 89185211327466598763751082139622197329899936691248485807696818388034044794163400342654203502792451207654942077749308827985800404384083870148626084445617

private def left : Mark := ⟨(-199779641185415334873048724560326701428481325130182963858731647318535779192106482049936037680395507386126589079562893712242034889240265045281690761695939),209379120756399659662664637030925134122936810321690582341555520348587379535262135226372897000968789795130501940026087683923251833608147357811726220561909,(-27469283836962790605308522891604597113467704959024512592737476342392738422662276665104156312633134880682299807662728292181438536361551687970865523680981),(-44592605663733299381875541069811098664949968345624242903848409194017022397081700171327101751396225603827471038874654413992900202192041935074313042222809)⟩
private def right : Mark := ⟨(-2657229638043431081108031838543682231084714813555850141517783749826841346124785534508388442971495699996885047056248613078771446931098624052014412352547),456152681762851205332799902309925274531598522145223401425068123420866648107804307023421341432396827592911359828623005374221666465407725926366406088014436,(-52345164661622249910575704568135026821820502803799647341156557208728177257446345958934564525861659147373899749045939709057546007965980768401998513426093),1745213724590071130874623139471071663577967069023341301808390536204370736680188845399579025481154728726359367434997043498376333573745909422606696960497⟩

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

theorem negative_transport_400_416 : Transports 400 416 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_400_416
