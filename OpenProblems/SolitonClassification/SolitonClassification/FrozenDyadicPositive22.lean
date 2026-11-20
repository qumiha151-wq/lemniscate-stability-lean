import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [96,96,96,96,100,100,100,100,100,100,100,100,100,104,104,104]
  170799849235629730767011435654555690008430954952777187548170450543191711679887097515596664779869289049676558908190827571720160981151509280091574865363156 733012777080986313392298986811721986378551631547720562105405351961320196686201287297237241513847225959460917451352987689278260100869048201379770522537172 89864178107748867709347483857306006274358698742818551739547040736104467286692682484350977489203023750535624632276930909670306434961701803896884835671045 53820791805826923384334080599599309638322074207601237871819595433886886241971328353193280671249964262400251531794735682118504137957795612458628357794179

private def left : Mark := ⟨85399924617814865383505717827277845004215477476388593774085225271595855839943548757798332389934644524838279454095413785860080490575754640045787432681578,366506388540493156696149493405860993189275815773860281052702675980660098343100643648618620756923612979730458725676493844639130050434524100689885261268586,(-44932089053874433854673741928653003137179349371409275869773520368052233643346341242175488744601511875267812316138465454835153217480850901948442417835523),(-26910395902913461692167040299799654819161037103800618935909797716943443120985664176596640335624982131200125765897367841059252068978897806229314178897090)⟩
private def right : Mark := ⟨199051575578015379729665141869569458353985330409495359039462380237301377244802867860501272587744412806175922123928112824053928370514986565548638806827317,(-51450660842785530063036961630787285122100592840884586149297962018598790682424474464746709489894884311553569645520644540580920689429488648899533841838450),24878939280463093364396063119896185449889980941054532026640174228204613033934262760924797803742218472011701660173522616784921323431466477142970721091655,(-46087963880777754313753680540063439619261735565009530847624674167795655939042721708858270681964690438030585383531437817467090160831880540209745564908925)⟩

private theorem cell0 : Transports 352 353 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 352 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 353 354 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 353 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 354 355 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 354 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 355 356 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 355 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 356 357 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 356 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 357 358 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 357 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 358 359 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 358 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 359 360 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 359 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 360 361 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 360 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 361 362 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 361 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 362 363 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 362 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 363 364 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 363 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 364 365 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 364 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 365 366 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 365 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 366 367 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 366 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 367 368 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 367 _ _ (by decide) (by decide +kernel)

theorem positive_transport_352_368 : Transports 352 368 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_352_368
