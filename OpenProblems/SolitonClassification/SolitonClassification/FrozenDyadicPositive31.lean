import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [104,104,104,104,100,100,100,100,100,96,96,96,96,96,100,100]
  357750767407382239552522889896700414262643665492088083319595572409195061572120014700761189359235928888027941136528859328486969433414250808682153536441279 829752348794051794894943518888536044293771815258727872538202839061924606546714778936048463860931331728113326347571667668864509319875790674805878908965636 63784346054018210463512296657062327723309722191989963881817431911287134516140903613608960004716041614900456063778027773239075250152971257348194828107755 83089140903301129934850671752401812702047975931761785504477760257267569503835343804213969261020138447140260851475029537984969321245843389887623336119577

private def left : Mark := ⟨(-178875383703691119776261444948350207131321832746044041659797786204597530786060007350380594679617964444013970568264429664243484716707125404341076768220640),414876174397025897447471759444268022146885907629363936269101419530962303273357389468024231930465665864056663173785833834432254659937895337402939454482818,(-31892173027009105231756148328531163861654861095994981940908715955643567258070451806804480002358020807450228031889013886619537625076485628674097414053878),(-41544570451650564967425335876200906351023987965880892752238880128633784751917671902106984630510069223570130425737514768992484660622921694943811668059789)⟩
private def right : Mark := ⟨76529773704998523952436688149346447113501396766594315351755557116289852926385902621502021528223153117306144815457879384423958079113597855313311159975090,534962775273957232983289068382260522503486608785677354874010900898659979216574680998572052239196780586481593973810331656706711318505992909712243046386267,(-48404908771547002205772720615175338921362047774848690857592270962330874583014665461602585471803200638314950266403210179477779687321280880894325741983989),(-20000671019119744209711156032205983924174125351753245771885689113611955196376561115130557116165760216282129575645247978767787722221865921767384990021728)⟩

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

theorem positive_transport_496_512 : Transports 496 512 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_496_512
