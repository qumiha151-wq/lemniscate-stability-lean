import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [96,96,92,92,92,92,92,96,96,96,96,96,100,100,100,100]
  106423032426232197106928654850769276544201557751736535036940342394853900448681690836162165927559196490391501694727843494958789080260771729882461898262214 798226733103267147969528455789262162341158110388329840795500917697239902908513453868170960149306344709015789720476950644800480337303078059927617421593677 101161596543999450940340532187092811227927618200772600766901157967915843862973968401415583621821465865739378709530101879169619539504874439200278953339542 27176819575815999262373326940610202534873988571350051018681560347276553600532648999820524529157839783386959016054563744768863632601019079486478228584938

private def left : Mark := ⟨53211516213116098553464327425384638272100778875868267518470171197426950224340845418081082963779598245195750847363921747479394540130385864941230949131107,(-399113366551633573984764227894631081170579055194164920397750458848619951454256726934085480074653172354507894860238475322400240168651539029963808710796839),50580798271999725470170266093546405613963809100386300383450578983957921931486984200707791810910732932869689354765050939584809769752437219600139476669771,13588409787907999631186663470305101267436994285675025509340780173638276800266324499910262264578919891693479508027281872384431816300509539743239114292469⟩
private def right : Mark := ⟨(-148835412508686991276617656455786693752402413523352121253624394040319477814802850066644381564555914132386828755746360537943012797389093557013147795592904),(-368541387217615694465326697067093192740583828917525560794261060761122934750674112618559278598162498323186099340987336836984734915445352860427863733925697),51340443115722328173604493947514699153778514312211709018017035312883993542247622461318696948234321332034827442012407329328364984498025975036523849900829,(-10354754225867658969572829406014280938842259239447127000168746590848174221015609024074874580917741475319720265692241869696823212468069404759305677976784)⟩

private theorem cell0 : Transports 384 385 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 384 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 385 386 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 385 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 386 387 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 386 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 387 388 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 387 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 388 389 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 388 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 389 390 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 389 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 390 391 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 390 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 391 392 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 391 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 392 393 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 392 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 393 394 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 393 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 394 395 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 394 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 395 396 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 395 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 396 397 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 396 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 397 398 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 397 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 398 399 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 398 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 399 400 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 399 _ _ (by decide) (by decide +kernel)

theorem positive_transport_384_400 : Transports 384 400 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_384_400
