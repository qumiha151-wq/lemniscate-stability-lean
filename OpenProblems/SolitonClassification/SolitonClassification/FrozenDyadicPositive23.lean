import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [104,104,100,100,100,100,100,100,100,100,100,96,96,96,96,96]
  398103151156030759459330283739138916707970660818990718078924760474602754489605735721002545175488825612351844247856225648107856741029973131097277613654634 102901321685571060126073923261574570244201185681769172298595924037197581364848948929493418979789768623107139291041289081161841378858977297799067683676899 49757878560926186728792126239792370899779961882109064053280348456409226067868525521849595607484436944023403320347045233569842646862932954285941442183310 92175927761555508627507361080126879238523471130019061695249348335591311878085443417716541363929380876061170767062875634934180321663761080419491129817849

private def left : Mark := ⟨199051575578015379729665141869569458353985330409495359039462380237301377244802867860501272587744412806175922123928112824053928370514986565548638806827317,(-51450660842785530063036961630787285122100592840884586149297962018598790682424474464746709489894884311553569645520644540580920689429488648899533841838450),24878939280463093364396063119896185449889980941054532026640174228204613033934262760924797803742218472011701660173522616784921323431466477142970721091655,(-46087963880777754313753680540063439619261735565009530847624674167795655939042721708858270681964690438030585383531437817467090160831880540209745564908925)⟩
private def right : Mark := ⟨53211516213116098553464327425384638272100778875868267518470171197426950224340845418081082963779598245195750847363921747479394540130385864941230949131107,(-399113366551633573984764227894631081170579055194164920397750458848619951454256726934085480074653172354507894860238475322400240168651539029963808710796839),50580798271999725470170266093546405613963809100386300383450578983957921931486984200707791810910732932869689354765050939584809769752437219600139476669771,13588409787907999631186663470305101267436994285675025509340780173638276800266324499910262264578919891693479508027281872384431816300509539743239114292469⟩

private theorem cell0 : Transports 368 369 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 368 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 369 370 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 369 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 370 371 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 370 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 371 372 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 371 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 372 373 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 372 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 373 374 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 373 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 374 375 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 374 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 375 376 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 375 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 376 377 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 376 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 377 378 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 377 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 378 379 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 378 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 379 380 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 379 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 380 381 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 380 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 381 382 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 381 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 382 383 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 382 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 383 384 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 383 _ _ (by decide) (by decide +kernel)

theorem positive_transport_368_384 : Transports 368 384 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_368_384
