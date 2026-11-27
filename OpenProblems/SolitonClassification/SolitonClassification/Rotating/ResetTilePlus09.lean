import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus0576
import SolitonClassification.Rotating.ResetPackedPlus0592
import SolitonClassification.Rotating.ResetPackedPlus0608
import SolitonClassification.Rotating.ResetPackedPlus0624
namespace SolitonClassification.Rotating.DyadicReset.TilePlus09
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus0576.p576,GridPlus.atNode 576,GridPlus.atNode 577,NodePlus09.w0,CompactPlus0576.checked576,CompactPlus0576.small576,CompactPlus0576.nodes576,NodePlus09.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus0576.p577,GridPlus.atNode 577,GridPlus.atNode 578,NodePlus09.w1,CompactPlus0576.checked577,CompactPlus0576.small577,CompactPlus0576.nodes577,NodePlus09.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus0576.p578,GridPlus.atNode 578,GridPlus.atNode 579,NodePlus09.w2,CompactPlus0576.checked578,CompactPlus0576.small578,CompactPlus0576.nodes578,NodePlus09.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus0576.p579,GridPlus.atNode 579,GridPlus.atNode 580,NodePlus09.w3,CompactPlus0576.checked579,CompactPlus0576.small579,CompactPlus0576.nodes579,NodePlus09.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus0576.p580,GridPlus.atNode 580,GridPlus.atNode 581,NodePlus09.w4,CompactPlus0576.checked580,CompactPlus0576.small580,CompactPlus0576.nodes580,NodePlus09.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus0576.p581,GridPlus.atNode 581,GridPlus.atNode 582,NodePlus09.w5,CompactPlus0576.checked581,CompactPlus0576.small581,CompactPlus0576.nodes581,NodePlus09.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus0576.p582,GridPlus.atNode 582,GridPlus.atNode 583,NodePlus09.w6,CompactPlus0576.checked582,CompactPlus0576.small582,CompactPlus0576.nodes582,NodePlus09.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus0576.p583,GridPlus.atNode 583,GridPlus.atNode 584,NodePlus09.w7,CompactPlus0576.checked583,CompactPlus0576.small583,CompactPlus0576.nodes583,NodePlus09.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus0576.p584,GridPlus.atNode 584,GridPlus.atNode 585,NodePlus09.w8,CompactPlus0576.checked584,CompactPlus0576.small584,CompactPlus0576.nodes584,NodePlus09.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus0576.p585,GridPlus.atNode 585,GridPlus.atNode 586,NodePlus09.w9,CompactPlus0576.checked585,CompactPlus0576.small585,CompactPlus0576.nodes585,NodePlus09.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus0576.p586,GridPlus.atNode 586,GridPlus.atNode 587,NodePlus09.w10,CompactPlus0576.checked586,CompactPlus0576.small586,CompactPlus0576.nodes586,NodePlus09.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus0576.p587,GridPlus.atNode 587,GridPlus.atNode 588,NodePlus09.w11,CompactPlus0576.checked587,CompactPlus0576.small587,CompactPlus0576.nodes587,NodePlus09.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus0576.p588,GridPlus.atNode 588,GridPlus.atNode 589,NodePlus09.w12,CompactPlus0576.checked588,CompactPlus0576.small588,CompactPlus0576.nodes588,NodePlus09.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus0576.p589,GridPlus.atNode 589,GridPlus.atNode 590,NodePlus09.w13,CompactPlus0576.checked589,CompactPlus0576.small589,CompactPlus0576.nodes589,NodePlus09.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus0576.p590,GridPlus.atNode 590,GridPlus.atNode 591,NodePlus09.w14,CompactPlus0576.checked590,CompactPlus0576.small590,CompactPlus0576.nodes590,NodePlus09.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus0576.p591,GridPlus.atNode 591,GridPlus.atNode 592,NodePlus09.w15,CompactPlus0576.checked591,CompactPlus0576.small591,CompactPlus0576.nodes591,NodePlus09.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus0592.p592,GridPlus.atNode 592,GridPlus.atNode 593,NodePlus09.w16,CompactPlus0592.checked592,CompactPlus0592.small592,CompactPlus0592.nodes592,NodePlus09.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus0592.p593,GridPlus.atNode 593,GridPlus.atNode 594,NodePlus09.w17,CompactPlus0592.checked593,CompactPlus0592.small593,CompactPlus0592.nodes593,NodePlus09.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus0592.p594,GridPlus.atNode 594,GridPlus.atNode 595,NodePlus09.w18,CompactPlus0592.checked594,CompactPlus0592.small594,CompactPlus0592.nodes594,NodePlus09.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus0592.p595,GridPlus.atNode 595,GridPlus.atNode 596,NodePlus09.w19,CompactPlus0592.checked595,CompactPlus0592.small595,CompactPlus0592.nodes595,NodePlus09.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus0592.p596,GridPlus.atNode 596,GridPlus.atNode 597,NodePlus09.w20,CompactPlus0592.checked596,CompactPlus0592.small596,CompactPlus0592.nodes596,NodePlus09.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus0592.p597,GridPlus.atNode 597,GridPlus.atNode 598,NodePlus09.w21,CompactPlus0592.checked597,CompactPlus0592.small597,CompactPlus0592.nodes597,NodePlus09.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus0592.p598,GridPlus.atNode 598,GridPlus.atNode 599,NodePlus09.w22,CompactPlus0592.checked598,CompactPlus0592.small598,CompactPlus0592.nodes598,NodePlus09.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus0592.p599,GridPlus.atNode 599,GridPlus.atNode 600,NodePlus09.w23,CompactPlus0592.checked599,CompactPlus0592.small599,CompactPlus0592.nodes599,NodePlus09.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus0592.p600,GridPlus.atNode 600,GridPlus.atNode 601,NodePlus09.w24,CompactPlus0592.checked600,CompactPlus0592.small600,CompactPlus0592.nodes600,NodePlus09.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus0592.p601,GridPlus.atNode 601,GridPlus.atNode 602,NodePlus09.w25,CompactPlus0592.checked601,CompactPlus0592.small601,CompactPlus0592.nodes601,NodePlus09.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus0592.p602,GridPlus.atNode 602,GridPlus.atNode 603,NodePlus09.w26,CompactPlus0592.checked602,CompactPlus0592.small602,CompactPlus0592.nodes602,NodePlus09.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus0592.p603,GridPlus.atNode 603,GridPlus.atNode 604,NodePlus09.w27,CompactPlus0592.checked603,CompactPlus0592.small603,CompactPlus0592.nodes603,NodePlus09.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus0592.p604,GridPlus.atNode 604,GridPlus.atNode 605,NodePlus09.w28,CompactPlus0592.checked604,CompactPlus0592.small604,CompactPlus0592.nodes604,NodePlus09.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus0592.p605,GridPlus.atNode 605,GridPlus.atNode 606,NodePlus09.w29,CompactPlus0592.checked605,CompactPlus0592.small605,CompactPlus0592.nodes605,NodePlus09.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus0592.p606,GridPlus.atNode 606,GridPlus.atNode 607,NodePlus09.w30,CompactPlus0592.checked606,CompactPlus0592.small606,CompactPlus0592.nodes606,NodePlus09.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus0592.p607,GridPlus.atNode 607,GridPlus.atNode 608,NodePlus09.w31,CompactPlus0592.checked607,CompactPlus0592.small607,CompactPlus0592.nodes607,NodePlus09.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus0608.p608,GridPlus.atNode 608,GridPlus.atNode 609,NodePlus09.w32,CompactPlus0608.checked608,CompactPlus0608.small608,CompactPlus0608.nodes608,NodePlus09.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus0608.p609,GridPlus.atNode 609,GridPlus.atNode 610,NodePlus09.w33,CompactPlus0608.checked609,CompactPlus0608.small609,CompactPlus0608.nodes609,NodePlus09.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus0608.p610,GridPlus.atNode 610,GridPlus.atNode 611,NodePlus09.w34,CompactPlus0608.checked610,CompactPlus0608.small610,CompactPlus0608.nodes610,NodePlus09.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus0608.p611,GridPlus.atNode 611,GridPlus.atNode 612,NodePlus09.w35,CompactPlus0608.checked611,CompactPlus0608.small611,CompactPlus0608.nodes611,NodePlus09.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus0608.p612,GridPlus.atNode 612,GridPlus.atNode 613,NodePlus09.w36,CompactPlus0608.checked612,CompactPlus0608.small612,CompactPlus0608.nodes612,NodePlus09.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus0608.p613,GridPlus.atNode 613,GridPlus.atNode 614,NodePlus09.w37,CompactPlus0608.checked613,CompactPlus0608.small613,CompactPlus0608.nodes613,NodePlus09.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus0608.p614,GridPlus.atNode 614,GridPlus.atNode 615,NodePlus09.w38,CompactPlus0608.checked614,CompactPlus0608.small614,CompactPlus0608.nodes614,NodePlus09.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus0608.p615,GridPlus.atNode 615,GridPlus.atNode 616,NodePlus09.w39,CompactPlus0608.checked615,CompactPlus0608.small615,CompactPlus0608.nodes615,NodePlus09.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus0608.p616,GridPlus.atNode 616,GridPlus.atNode 617,NodePlus09.w40,CompactPlus0608.checked616,CompactPlus0608.small616,CompactPlus0608.nodes616,NodePlus09.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus0608.p617,GridPlus.atNode 617,GridPlus.atNode 618,NodePlus09.w41,CompactPlus0608.checked617,CompactPlus0608.small617,CompactPlus0608.nodes617,NodePlus09.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus0608.p618,GridPlus.atNode 618,GridPlus.atNode 619,NodePlus09.w42,CompactPlus0608.checked618,CompactPlus0608.small618,CompactPlus0608.nodes618,NodePlus09.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus0608.p619,GridPlus.atNode 619,GridPlus.atNode 620,NodePlus09.w43,CompactPlus0608.checked619,CompactPlus0608.small619,CompactPlus0608.nodes619,NodePlus09.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus0608.p620,GridPlus.atNode 620,GridPlus.atNode 621,NodePlus09.w44,CompactPlus0608.checked620,CompactPlus0608.small620,CompactPlus0608.nodes620,NodePlus09.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus0608.p621,GridPlus.atNode 621,GridPlus.atNode 622,NodePlus09.w45,CompactPlus0608.checked621,CompactPlus0608.small621,CompactPlus0608.nodes621,NodePlus09.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus0608.p622,GridPlus.atNode 622,GridPlus.atNode 623,NodePlus09.w46,CompactPlus0608.checked622,CompactPlus0608.small622,CompactPlus0608.nodes622,NodePlus09.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus0608.p623,GridPlus.atNode 623,GridPlus.atNode 624,NodePlus09.w47,CompactPlus0608.checked623,CompactPlus0608.small623,CompactPlus0608.nodes623,NodePlus09.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus0624.p624,GridPlus.atNode 624,GridPlus.atNode 625,NodePlus09.w48,CompactPlus0624.checked624,CompactPlus0624.small624,CompactPlus0624.nodes624,NodePlus09.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus0624.p625,GridPlus.atNode 625,GridPlus.atNode 626,NodePlus09.w49,CompactPlus0624.checked625,CompactPlus0624.small625,CompactPlus0624.nodes625,NodePlus09.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus0624.p626,GridPlus.atNode 626,GridPlus.atNode 627,NodePlus09.w50,CompactPlus0624.checked626,CompactPlus0624.small626,CompactPlus0624.nodes626,NodePlus09.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus0624.p627,GridPlus.atNode 627,GridPlus.atNode 628,NodePlus09.w51,CompactPlus0624.checked627,CompactPlus0624.small627,CompactPlus0624.nodes627,NodePlus09.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus0624.p628,GridPlus.atNode 628,GridPlus.atNode 629,NodePlus09.w52,CompactPlus0624.checked628,CompactPlus0624.small628,CompactPlus0624.nodes628,NodePlus09.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus0624.p629,GridPlus.atNode 629,GridPlus.atNode 630,NodePlus09.w53,CompactPlus0624.checked629,CompactPlus0624.small629,CompactPlus0624.nodes629,NodePlus09.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus0624.p630,GridPlus.atNode 630,GridPlus.atNode 631,NodePlus09.w54,CompactPlus0624.checked630,CompactPlus0624.small630,CompactPlus0624.nodes630,NodePlus09.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus0624.p631,GridPlus.atNode 631,GridPlus.atNode 632,NodePlus09.w55,CompactPlus0624.checked631,CompactPlus0624.small631,CompactPlus0624.nodes631,NodePlus09.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus0624.p632,GridPlus.atNode 632,GridPlus.atNode 633,NodePlus09.w56,CompactPlus0624.checked632,CompactPlus0624.small632,CompactPlus0624.nodes632,NodePlus09.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus0624.p633,GridPlus.atNode 633,GridPlus.atNode 634,NodePlus09.w57,CompactPlus0624.checked633,CompactPlus0624.small633,CompactPlus0624.nodes633,NodePlus09.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus0624.p634,GridPlus.atNode 634,GridPlus.atNode 635,NodePlus09.w58,CompactPlus0624.checked634,CompactPlus0624.small634,CompactPlus0624.nodes634,NodePlus09.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus0624.p635,GridPlus.atNode 635,GridPlus.atNode 636,NodePlus09.w59,CompactPlus0624.checked635,CompactPlus0624.small635,CompactPlus0624.nodes635,NodePlus09.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus0624.p636,GridPlus.atNode 636,GridPlus.atNode 637,NodePlus09.w60,CompactPlus0624.checked636,CompactPlus0624.small636,CompactPlus0624.nodes636,NodePlus09.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus0624.p637,GridPlus.atNode 637,GridPlus.atNode 638,NodePlus09.w61,CompactPlus0624.checked637,CompactPlus0624.small637,CompactPlus0624.nodes637,NodePlus09.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus0624.p638,GridPlus.atNode 638,GridPlus.atNode 639,NodePlus09.w62,CompactPlus0624.checked638,CompactPlus0624.small638,CompactPlus0624.nodes638,NodePlus09.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus0624.p639,GridPlus.atNode 639,GridPlus.atNode 640,NodePlus09.w63,CompactPlus0624.checked639,CompactPlus0624.small639,CompactPlus0624.nodes639,NodePlus09.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (576+j) ∧
    (atRow j).right=GridPlus.atNode (576+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus09
