import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [108,108,112,112,112,112,112,112,112,112,112,112,112,108,108,108]
  399527058980480578481550072416037394569293623842197372725910943751969270593916627486057939670375833056856792870231809417720872044786605799382515632381635 1073541236088595232464545221287921993859388783916329394390374724442982239724398485436973034101074138549605466583867217507085954886644644080004564990282555 97969447860230393637634240936617453845220583410471728022472316920442162757304966829755728405840777792553701394610819968084377605987610335402573922952170 37070681455146946245930979009645515780705274832832373124425422904731776643251816576604339545203239672787152735452687645764859424189916311145954471229733

private def left : Mark := ⟨(-199763529490240289240775036208018697284646811921098686362955471875984635296958313743028969835187916528428396435115904708860436022393302899691257816190818),(-536770618044297616232272610643960996929694391958164697195187362221491119862199242718486517050537069274802733291933608753542977443322322040002282495141278),48984723930115196818817120468308726922610291705235864011236158460221081378652483414877864202920388896276850697305409984042188802993805167701286961476085,(-18535340727573473122965489504822757890352637416416186562212711452365888321625908288302169772601619836393576367726343822882429712094958155572977235614867)⟩
private def right : Mark := ⟨(-150496231212480689008753227791347345220143676715606499317136332211053729634035309760887218277397702481148683828530979389819681625757823118990849343179754),630872809851935874666458041159753723877872021812835830467718726409689002744876817859812997331604149085904081516633868821245751626741697872914022228625591,(-43754922016443450616227503019675631765701781854845174374360249042680484115991203203306741804801880365220871789471033860055101921602745189967016194567975),(-28784871612216660069460959770464750960038433591376304365176673133935591872650587656749822711264706863613192109982569669710730041717916669099531731464858)⟩

private theorem cell0 : Transports 624 625 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 624 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 625 626 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 625 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 626 627 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 626 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 627 628 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 627 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 628 629 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 628 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 629 630 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 629 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 630 631 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 630 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 631 632 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 631 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 632 633 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 632 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 633 634 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 633 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 634 635 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 634 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 635 636 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 635 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 636 637 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 636 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 637 638 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 637 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 638 639 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 638 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 639 640 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 639 _ _ (by decide) (by decide +kernel)

theorem positive_transport_624_640 : Transports 624 640 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_624_640
