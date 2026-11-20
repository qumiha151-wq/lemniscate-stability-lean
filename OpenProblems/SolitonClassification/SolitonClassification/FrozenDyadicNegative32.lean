import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [108,108,108,108,108,108,108,108,104,104,104,104,100,100,100,100]
  484162679950772478082404042169076159603066104754569553610805165934396970271671904135492199478360598628768207695961674762603821707857475248730292907694724 74441435199022401443249265550156817238845319412563095138975837129472197311607946470457577656657918760862029173886327461352892415939367820422158323958935 5213223261102659034352277558212588062402875542153555546323793771520602753436389226386864686610705310071048325379954832013558200872413952162223731618080 104618690685829535110299300015218216811996065532674421156160007543455442249504842041723371563606819854689633578213795284133334197711005261088530779165791

private def left : Mark := ⟨242081339975386239041202021084538079801533052377284776805402582967198485135835952067746099739180299314384103847980837381301910853928737624365146453847362,(-37220717599511200721624632775078408619422659706281547569487918564736098655803973235228788828328959380431014586943163730676446207969683910211079161979468),2606611630551329517176138779106294031201437771076777773161896885760301376718194613193432343305352655035524162689977416006779100436206976081111865809040,(-52309345342914767555149650007609108405998032766337210578080003771727721124752421020861685781803409927344816789106897642066667098855502630544265389582896)⟩
private def right : Mark := ⟨25907711846676552409342059732995057982171488012477380427661869897782650600897902299510394592331790083563637102599416046534387179061754199571432407866771,(-577619978760425747839087262249684555314624948349022916014198739822380150901771171945723431932896318316927854748922378814984426757735409757385567359755037),52331193775068397259104624298245710635368930549399003013256799994389427888764549341751824555953610269223027771507536730154719404241992644221828503921920,(-2123250449920350437978512863539495200761673341001117984920171999729736615329806828601595207046390380578521381115744340233790925367707643874675091991270)⟩

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

theorem negative_transport_512_528 : Transports 512 528 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_transport_512_528
