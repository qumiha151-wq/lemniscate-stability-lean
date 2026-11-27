import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus0576
import SolitonClassification.Rotating.ResetPackedMinus0592
import SolitonClassification.Rotating.ResetPackedMinus0608
import SolitonClassification.Rotating.ResetPackedMinus0624
namespace SolitonClassification.Rotating.DyadicReset.TileMinus09
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0576.p576,GridMinus.atNode 576,GridMinus.atNode 577,NodeMinus09.w0,CompactMinus0576.checked576,CompactMinus0576.small576,CompactMinus0576.nodes576,NodeMinus09.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0576.p577,GridMinus.atNode 577,GridMinus.atNode 578,NodeMinus09.w1,CompactMinus0576.checked577,CompactMinus0576.small577,CompactMinus0576.nodes577,NodeMinus09.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0576.p578,GridMinus.atNode 578,GridMinus.atNode 579,NodeMinus09.w2,CompactMinus0576.checked578,CompactMinus0576.small578,CompactMinus0576.nodes578,NodeMinus09.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0576.p579,GridMinus.atNode 579,GridMinus.atNode 580,NodeMinus09.w3,CompactMinus0576.checked579,CompactMinus0576.small579,CompactMinus0576.nodes579,NodeMinus09.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0576.p580,GridMinus.atNode 580,GridMinus.atNode 581,NodeMinus09.w4,CompactMinus0576.checked580,CompactMinus0576.small580,CompactMinus0576.nodes580,NodeMinus09.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0576.p581,GridMinus.atNode 581,GridMinus.atNode 582,NodeMinus09.w5,CompactMinus0576.checked581,CompactMinus0576.small581,CompactMinus0576.nodes581,NodeMinus09.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0576.p582,GridMinus.atNode 582,GridMinus.atNode 583,NodeMinus09.w6,CompactMinus0576.checked582,CompactMinus0576.small582,CompactMinus0576.nodes582,NodeMinus09.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0576.p583,GridMinus.atNode 583,GridMinus.atNode 584,NodeMinus09.w7,CompactMinus0576.checked583,CompactMinus0576.small583,CompactMinus0576.nodes583,NodeMinus09.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0576.p584,GridMinus.atNode 584,GridMinus.atNode 585,NodeMinus09.w8,CompactMinus0576.checked584,CompactMinus0576.small584,CompactMinus0576.nodes584,NodeMinus09.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0576.p585,GridMinus.atNode 585,GridMinus.atNode 586,NodeMinus09.w9,CompactMinus0576.checked585,CompactMinus0576.small585,CompactMinus0576.nodes585,NodeMinus09.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0576.p586,GridMinus.atNode 586,GridMinus.atNode 587,NodeMinus09.w10,CompactMinus0576.checked586,CompactMinus0576.small586,CompactMinus0576.nodes586,NodeMinus09.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0576.p587,GridMinus.atNode 587,GridMinus.atNode 588,NodeMinus09.w11,CompactMinus0576.checked587,CompactMinus0576.small587,CompactMinus0576.nodes587,NodeMinus09.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0576.p588,GridMinus.atNode 588,GridMinus.atNode 589,NodeMinus09.w12,CompactMinus0576.checked588,CompactMinus0576.small588,CompactMinus0576.nodes588,NodeMinus09.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0576.p589,GridMinus.atNode 589,GridMinus.atNode 590,NodeMinus09.w13,CompactMinus0576.checked589,CompactMinus0576.small589,CompactMinus0576.nodes589,NodeMinus09.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0576.p590,GridMinus.atNode 590,GridMinus.atNode 591,NodeMinus09.w14,CompactMinus0576.checked590,CompactMinus0576.small590,CompactMinus0576.nodes590,NodeMinus09.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0576.p591,GridMinus.atNode 591,GridMinus.atNode 592,NodeMinus09.w15,CompactMinus0576.checked591,CompactMinus0576.small591,CompactMinus0576.nodes591,NodeMinus09.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0592.p592,GridMinus.atNode 592,GridMinus.atNode 593,NodeMinus09.w16,CompactMinus0592.checked592,CompactMinus0592.small592,CompactMinus0592.nodes592,NodeMinus09.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0592.p593,GridMinus.atNode 593,GridMinus.atNode 594,NodeMinus09.w17,CompactMinus0592.checked593,CompactMinus0592.small593,CompactMinus0592.nodes593,NodeMinus09.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0592.p594,GridMinus.atNode 594,GridMinus.atNode 595,NodeMinus09.w18,CompactMinus0592.checked594,CompactMinus0592.small594,CompactMinus0592.nodes594,NodeMinus09.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0592.p595,GridMinus.atNode 595,GridMinus.atNode 596,NodeMinus09.w19,CompactMinus0592.checked595,CompactMinus0592.small595,CompactMinus0592.nodes595,NodeMinus09.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0592.p596,GridMinus.atNode 596,GridMinus.atNode 597,NodeMinus09.w20,CompactMinus0592.checked596,CompactMinus0592.small596,CompactMinus0592.nodes596,NodeMinus09.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0592.p597,GridMinus.atNode 597,GridMinus.atNode 598,NodeMinus09.w21,CompactMinus0592.checked597,CompactMinus0592.small597,CompactMinus0592.nodes597,NodeMinus09.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0592.p598,GridMinus.atNode 598,GridMinus.atNode 599,NodeMinus09.w22,CompactMinus0592.checked598,CompactMinus0592.small598,CompactMinus0592.nodes598,NodeMinus09.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0592.p599,GridMinus.atNode 599,GridMinus.atNode 600,NodeMinus09.w23,CompactMinus0592.checked599,CompactMinus0592.small599,CompactMinus0592.nodes599,NodeMinus09.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0592.p600,GridMinus.atNode 600,GridMinus.atNode 601,NodeMinus09.w24,CompactMinus0592.checked600,CompactMinus0592.small600,CompactMinus0592.nodes600,NodeMinus09.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0592.p601,GridMinus.atNode 601,GridMinus.atNode 602,NodeMinus09.w25,CompactMinus0592.checked601,CompactMinus0592.small601,CompactMinus0592.nodes601,NodeMinus09.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0592.p602,GridMinus.atNode 602,GridMinus.atNode 603,NodeMinus09.w26,CompactMinus0592.checked602,CompactMinus0592.small602,CompactMinus0592.nodes602,NodeMinus09.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0592.p603,GridMinus.atNode 603,GridMinus.atNode 604,NodeMinus09.w27,CompactMinus0592.checked603,CompactMinus0592.small603,CompactMinus0592.nodes603,NodeMinus09.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0592.p604,GridMinus.atNode 604,GridMinus.atNode 605,NodeMinus09.w28,CompactMinus0592.checked604,CompactMinus0592.small604,CompactMinus0592.nodes604,NodeMinus09.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0592.p605,GridMinus.atNode 605,GridMinus.atNode 606,NodeMinus09.w29,CompactMinus0592.checked605,CompactMinus0592.small605,CompactMinus0592.nodes605,NodeMinus09.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0592.p606,GridMinus.atNode 606,GridMinus.atNode 607,NodeMinus09.w30,CompactMinus0592.checked606,CompactMinus0592.small606,CompactMinus0592.nodes606,NodeMinus09.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0592.p607,GridMinus.atNode 607,GridMinus.atNode 608,NodeMinus09.w31,CompactMinus0592.checked607,CompactMinus0592.small607,CompactMinus0592.nodes607,NodeMinus09.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0608.p608,GridMinus.atNode 608,GridMinus.atNode 609,NodeMinus09.w32,CompactMinus0608.checked608,CompactMinus0608.small608,CompactMinus0608.nodes608,NodeMinus09.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0608.p609,GridMinus.atNode 609,GridMinus.atNode 610,NodeMinus09.w33,CompactMinus0608.checked609,CompactMinus0608.small609,CompactMinus0608.nodes609,NodeMinus09.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0608.p610,GridMinus.atNode 610,GridMinus.atNode 611,NodeMinus09.w34,CompactMinus0608.checked610,CompactMinus0608.small610,CompactMinus0608.nodes610,NodeMinus09.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0608.p611,GridMinus.atNode 611,GridMinus.atNode 612,NodeMinus09.w35,CompactMinus0608.checked611,CompactMinus0608.small611,CompactMinus0608.nodes611,NodeMinus09.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0608.p612,GridMinus.atNode 612,GridMinus.atNode 613,NodeMinus09.w36,CompactMinus0608.checked612,CompactMinus0608.small612,CompactMinus0608.nodes612,NodeMinus09.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0608.p613,GridMinus.atNode 613,GridMinus.atNode 614,NodeMinus09.w37,CompactMinus0608.checked613,CompactMinus0608.small613,CompactMinus0608.nodes613,NodeMinus09.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0608.p614,GridMinus.atNode 614,GridMinus.atNode 615,NodeMinus09.w38,CompactMinus0608.checked614,CompactMinus0608.small614,CompactMinus0608.nodes614,NodeMinus09.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0608.p615,GridMinus.atNode 615,GridMinus.atNode 616,NodeMinus09.w39,CompactMinus0608.checked615,CompactMinus0608.small615,CompactMinus0608.nodes615,NodeMinus09.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0608.p616,GridMinus.atNode 616,GridMinus.atNode 617,NodeMinus09.w40,CompactMinus0608.checked616,CompactMinus0608.small616,CompactMinus0608.nodes616,NodeMinus09.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0608.p617,GridMinus.atNode 617,GridMinus.atNode 618,NodeMinus09.w41,CompactMinus0608.checked617,CompactMinus0608.small617,CompactMinus0608.nodes617,NodeMinus09.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0608.p618,GridMinus.atNode 618,GridMinus.atNode 619,NodeMinus09.w42,CompactMinus0608.checked618,CompactMinus0608.small618,CompactMinus0608.nodes618,NodeMinus09.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0608.p619,GridMinus.atNode 619,GridMinus.atNode 620,NodeMinus09.w43,CompactMinus0608.checked619,CompactMinus0608.small619,CompactMinus0608.nodes619,NodeMinus09.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0608.p620,GridMinus.atNode 620,GridMinus.atNode 621,NodeMinus09.w44,CompactMinus0608.checked620,CompactMinus0608.small620,CompactMinus0608.nodes620,NodeMinus09.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0608.p621,GridMinus.atNode 621,GridMinus.atNode 622,NodeMinus09.w45,CompactMinus0608.checked621,CompactMinus0608.small621,CompactMinus0608.nodes621,NodeMinus09.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0608.p622,GridMinus.atNode 622,GridMinus.atNode 623,NodeMinus09.w46,CompactMinus0608.checked622,CompactMinus0608.small622,CompactMinus0608.nodes622,NodeMinus09.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0608.p623,GridMinus.atNode 623,GridMinus.atNode 624,NodeMinus09.w47,CompactMinus0608.checked623,CompactMinus0608.small623,CompactMinus0608.nodes623,NodeMinus09.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0624.p624,GridMinus.atNode 624,GridMinus.atNode 625,NodeMinus09.w48,CompactMinus0624.checked624,CompactMinus0624.small624,CompactMinus0624.nodes624,NodeMinus09.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0624.p625,GridMinus.atNode 625,GridMinus.atNode 626,NodeMinus09.w49,CompactMinus0624.checked625,CompactMinus0624.small625,CompactMinus0624.nodes625,NodeMinus09.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0624.p626,GridMinus.atNode 626,GridMinus.atNode 627,NodeMinus09.w50,CompactMinus0624.checked626,CompactMinus0624.small626,CompactMinus0624.nodes626,NodeMinus09.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0624.p627,GridMinus.atNode 627,GridMinus.atNode 628,NodeMinus09.w51,CompactMinus0624.checked627,CompactMinus0624.small627,CompactMinus0624.nodes627,NodeMinus09.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0624.p628,GridMinus.atNode 628,GridMinus.atNode 629,NodeMinus09.w52,CompactMinus0624.checked628,CompactMinus0624.small628,CompactMinus0624.nodes628,NodeMinus09.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0624.p629,GridMinus.atNode 629,GridMinus.atNode 630,NodeMinus09.w53,CompactMinus0624.checked629,CompactMinus0624.small629,CompactMinus0624.nodes629,NodeMinus09.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0624.p630,GridMinus.atNode 630,GridMinus.atNode 631,NodeMinus09.w54,CompactMinus0624.checked630,CompactMinus0624.small630,CompactMinus0624.nodes630,NodeMinus09.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0624.p631,GridMinus.atNode 631,GridMinus.atNode 632,NodeMinus09.w55,CompactMinus0624.checked631,CompactMinus0624.small631,CompactMinus0624.nodes631,NodeMinus09.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0624.p632,GridMinus.atNode 632,GridMinus.atNode 633,NodeMinus09.w56,CompactMinus0624.checked632,CompactMinus0624.small632,CompactMinus0624.nodes632,NodeMinus09.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0624.p633,GridMinus.atNode 633,GridMinus.atNode 634,NodeMinus09.w57,CompactMinus0624.checked633,CompactMinus0624.small633,CompactMinus0624.nodes633,NodeMinus09.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0624.p634,GridMinus.atNode 634,GridMinus.atNode 635,NodeMinus09.w58,CompactMinus0624.checked634,CompactMinus0624.small634,CompactMinus0624.nodes634,NodeMinus09.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0624.p635,GridMinus.atNode 635,GridMinus.atNode 636,NodeMinus09.w59,CompactMinus0624.checked635,CompactMinus0624.small635,CompactMinus0624.nodes635,NodeMinus09.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0624.p636,GridMinus.atNode 636,GridMinus.atNode 637,NodeMinus09.w60,CompactMinus0624.checked636,CompactMinus0624.small636,CompactMinus0624.nodes636,NodeMinus09.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0624.p637,GridMinus.atNode 637,GridMinus.atNode 638,NodeMinus09.w61,CompactMinus0624.checked637,CompactMinus0624.small637,CompactMinus0624.nodes637,NodeMinus09.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0624.p638,GridMinus.atNode 638,GridMinus.atNode 639,NodeMinus09.w62,CompactMinus0624.checked638,CompactMinus0624.small638,CompactMinus0624.nodes638,NodeMinus09.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0624.p639,GridMinus.atNode 639,GridMinus.atNode 640,NodeMinus09.w63,CompactMinus0624.checked639,CompactMinus0624.small639,CompactMinus0624.nodes639,NodeMinus09.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (576+j) ∧
    (atRow j).right=GridMinus.atNode (576+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus09
