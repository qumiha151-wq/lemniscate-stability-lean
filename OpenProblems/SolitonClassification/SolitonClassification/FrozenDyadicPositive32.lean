import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [100,100,104,104,104,104,104,104,108,108,108,108,108,108,108,108]
  153059547409997047904873376298692894227002793533188630703511114232579705852771805243004043056446306234612289630915758768847916158227195710626622319950180 1069925550547914465966578136764521045006973217571354709748021801797319958433149361997144104478393561172963187947620663313413422637011985819424486092772534 96809817543094004411545441230350677842724095549697381715184541924661749166029330923205170943606401276629900532806420358955559374642561761788651483967977 40001342038239488419422312064411967848348250703506491543771378227223910392753122230261114232331520432564259151290495957535575444443731843534769980043455

private def left : Mark := ⟨76529773704998523952436688149346447113501396766594315351755557116289852926385902621502021528223153117306144815457879384423958079113597855313311159975090,534962775273957232983289068382260522503486608785677354874010900898659979216574680998572052239196780586481593973810331656706711318505992909712243046386267,(-48404908771547002205772720615175338921362047774848690857592270962330874583014665461602585471803200638314950266403210179477779687321280880894325741983989),(-20000671019119744209711156032205983924174125351753245771885689113611955196376561115130557116165760216282129575645247978767787722221865921767384990021728)⟩
private def right : Mark := ⟨234444959089329932277477983502546902332305144538711034099290270579204746450389221806595990267502584024198327645301446271686215090192037815348375104690226,(-158767708017875816650830086622842393172485028109633651853830781439424099289966782028317284809796337093182497656608633907558186760435312840631884149800381),28994113315119266524419230292100746897236114753741483592567632043143760547785259538737381469191252671249807751726964505030353376844406542922337576052614,(-43616549926224884736559763594866694409345582373357825014578539727497078196888548183991156094578921189063797765879589122016857254949681184129570739154697)⟩

private theorem cell0 : Transports 512 513 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 512 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 513 514 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 513 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 514 515 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 514 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 515 516 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 515 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 516 517 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 516 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 517 518 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 517 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 518 519 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 518 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 519 520 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 519 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 520 521 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 520 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 521 522 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 521 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 522 523 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 522 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 523 524 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 523 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 524 525 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 524 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 525 526 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 525 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 526 527 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 526 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 527 528 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 527 _ _ (by decide) (by decide +kernel)

theorem positive_transport_512_528 : Transports 512 528 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_512_528
