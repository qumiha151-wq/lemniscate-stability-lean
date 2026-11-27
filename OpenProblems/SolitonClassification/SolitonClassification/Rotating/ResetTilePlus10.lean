import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus0640
import SolitonClassification.Rotating.ResetPackedPlus0656
import SolitonClassification.Rotating.ResetPackedPlus0672
import SolitonClassification.Rotating.ResetPackedPlus0688
namespace SolitonClassification.Rotating.DyadicReset.TilePlus10
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus0640.p640,GridPlus.atNode 640,GridPlus.atNode 641,NodePlus10.w0,CompactPlus0640.checked640,CompactPlus0640.small640,CompactPlus0640.nodes640,NodePlus10.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus0640.p641,GridPlus.atNode 641,GridPlus.atNode 642,NodePlus10.w1,CompactPlus0640.checked641,CompactPlus0640.small641,CompactPlus0640.nodes641,NodePlus10.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus0640.p642,GridPlus.atNode 642,GridPlus.atNode 643,NodePlus10.w2,CompactPlus0640.checked642,CompactPlus0640.small642,CompactPlus0640.nodes642,NodePlus10.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus0640.p643,GridPlus.atNode 643,GridPlus.atNode 644,NodePlus10.w3,CompactPlus0640.checked643,CompactPlus0640.small643,CompactPlus0640.nodes643,NodePlus10.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus0640.p644,GridPlus.atNode 644,GridPlus.atNode 645,NodePlus10.w4,CompactPlus0640.checked644,CompactPlus0640.small644,CompactPlus0640.nodes644,NodePlus10.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus0640.p645,GridPlus.atNode 645,GridPlus.atNode 646,NodePlus10.w5,CompactPlus0640.checked645,CompactPlus0640.small645,CompactPlus0640.nodes645,NodePlus10.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus0640.p646,GridPlus.atNode 646,GridPlus.atNode 647,NodePlus10.w6,CompactPlus0640.checked646,CompactPlus0640.small646,CompactPlus0640.nodes646,NodePlus10.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus0640.p647,GridPlus.atNode 647,GridPlus.atNode 648,NodePlus10.w7,CompactPlus0640.checked647,CompactPlus0640.small647,CompactPlus0640.nodes647,NodePlus10.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus0640.p648,GridPlus.atNode 648,GridPlus.atNode 649,NodePlus10.w8,CompactPlus0640.checked648,CompactPlus0640.small648,CompactPlus0640.nodes648,NodePlus10.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus0640.p649,GridPlus.atNode 649,GridPlus.atNode 650,NodePlus10.w9,CompactPlus0640.checked649,CompactPlus0640.small649,CompactPlus0640.nodes649,NodePlus10.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus0640.p650,GridPlus.atNode 650,GridPlus.atNode 651,NodePlus10.w10,CompactPlus0640.checked650,CompactPlus0640.small650,CompactPlus0640.nodes650,NodePlus10.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus0640.p651,GridPlus.atNode 651,GridPlus.atNode 652,NodePlus10.w11,CompactPlus0640.checked651,CompactPlus0640.small651,CompactPlus0640.nodes651,NodePlus10.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus0640.p652,GridPlus.atNode 652,GridPlus.atNode 653,NodePlus10.w12,CompactPlus0640.checked652,CompactPlus0640.small652,CompactPlus0640.nodes652,NodePlus10.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus0640.p653,GridPlus.atNode 653,GridPlus.atNode 654,NodePlus10.w13,CompactPlus0640.checked653,CompactPlus0640.small653,CompactPlus0640.nodes653,NodePlus10.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus0640.p654,GridPlus.atNode 654,GridPlus.atNode 655,NodePlus10.w14,CompactPlus0640.checked654,CompactPlus0640.small654,CompactPlus0640.nodes654,NodePlus10.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus0640.p655,GridPlus.atNode 655,GridPlus.atNode 656,NodePlus10.w15,CompactPlus0640.checked655,CompactPlus0640.small655,CompactPlus0640.nodes655,NodePlus10.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus0656.p656,GridPlus.atNode 656,GridPlus.atNode 657,NodePlus10.w16,CompactPlus0656.checked656,CompactPlus0656.small656,CompactPlus0656.nodes656,NodePlus10.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus0656.p657,GridPlus.atNode 657,GridPlus.atNode 658,NodePlus10.w17,CompactPlus0656.checked657,CompactPlus0656.small657,CompactPlus0656.nodes657,NodePlus10.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus0656.p658,GridPlus.atNode 658,GridPlus.atNode 659,NodePlus10.w18,CompactPlus0656.checked658,CompactPlus0656.small658,CompactPlus0656.nodes658,NodePlus10.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus0656.p659,GridPlus.atNode 659,GridPlus.atNode 660,NodePlus10.w19,CompactPlus0656.checked659,CompactPlus0656.small659,CompactPlus0656.nodes659,NodePlus10.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus0656.p660,GridPlus.atNode 660,GridPlus.atNode 661,NodePlus10.w20,CompactPlus0656.checked660,CompactPlus0656.small660,CompactPlus0656.nodes660,NodePlus10.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus0656.p661,GridPlus.atNode 661,GridPlus.atNode 662,NodePlus10.w21,CompactPlus0656.checked661,CompactPlus0656.small661,CompactPlus0656.nodes661,NodePlus10.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus0656.p662,GridPlus.atNode 662,GridPlus.atNode 663,NodePlus10.w22,CompactPlus0656.checked662,CompactPlus0656.small662,CompactPlus0656.nodes662,NodePlus10.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus0656.p663,GridPlus.atNode 663,GridPlus.atNode 664,NodePlus10.w23,CompactPlus0656.checked663,CompactPlus0656.small663,CompactPlus0656.nodes663,NodePlus10.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus0656.p664,GridPlus.atNode 664,GridPlus.atNode 665,NodePlus10.w24,CompactPlus0656.checked664,CompactPlus0656.small664,CompactPlus0656.nodes664,NodePlus10.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus0656.p665,GridPlus.atNode 665,GridPlus.atNode 666,NodePlus10.w25,CompactPlus0656.checked665,CompactPlus0656.small665,CompactPlus0656.nodes665,NodePlus10.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus0656.p666,GridPlus.atNode 666,GridPlus.atNode 667,NodePlus10.w26,CompactPlus0656.checked666,CompactPlus0656.small666,CompactPlus0656.nodes666,NodePlus10.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus0656.p667,GridPlus.atNode 667,GridPlus.atNode 668,NodePlus10.w27,CompactPlus0656.checked667,CompactPlus0656.small667,CompactPlus0656.nodes667,NodePlus10.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus0656.p668,GridPlus.atNode 668,GridPlus.atNode 669,NodePlus10.w28,CompactPlus0656.checked668,CompactPlus0656.small668,CompactPlus0656.nodes668,NodePlus10.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus0656.p669,GridPlus.atNode 669,GridPlus.atNode 670,NodePlus10.w29,CompactPlus0656.checked669,CompactPlus0656.small669,CompactPlus0656.nodes669,NodePlus10.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus0656.p670,GridPlus.atNode 670,GridPlus.atNode 671,NodePlus10.w30,CompactPlus0656.checked670,CompactPlus0656.small670,CompactPlus0656.nodes670,NodePlus10.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus0656.p671,GridPlus.atNode 671,GridPlus.atNode 672,NodePlus10.w31,CompactPlus0656.checked671,CompactPlus0656.small671,CompactPlus0656.nodes671,NodePlus10.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus0672.p672,GridPlus.atNode 672,GridPlus.atNode 673,NodePlus10.w32,CompactPlus0672.checked672,CompactPlus0672.small672,CompactPlus0672.nodes672,NodePlus10.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus0672.p673,GridPlus.atNode 673,GridPlus.atNode 674,NodePlus10.w33,CompactPlus0672.checked673,CompactPlus0672.small673,CompactPlus0672.nodes673,NodePlus10.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus0672.p674,GridPlus.atNode 674,GridPlus.atNode 675,NodePlus10.w34,CompactPlus0672.checked674,CompactPlus0672.small674,CompactPlus0672.nodes674,NodePlus10.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus0672.p675,GridPlus.atNode 675,GridPlus.atNode 676,NodePlus10.w35,CompactPlus0672.checked675,CompactPlus0672.small675,CompactPlus0672.nodes675,NodePlus10.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus0672.p676,GridPlus.atNode 676,GridPlus.atNode 677,NodePlus10.w36,CompactPlus0672.checked676,CompactPlus0672.small676,CompactPlus0672.nodes676,NodePlus10.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus0672.p677,GridPlus.atNode 677,GridPlus.atNode 678,NodePlus10.w37,CompactPlus0672.checked677,CompactPlus0672.small677,CompactPlus0672.nodes677,NodePlus10.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus0672.p678,GridPlus.atNode 678,GridPlus.atNode 679,NodePlus10.w38,CompactPlus0672.checked678,CompactPlus0672.small678,CompactPlus0672.nodes678,NodePlus10.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus0672.p679,GridPlus.atNode 679,GridPlus.atNode 680,NodePlus10.w39,CompactPlus0672.checked679,CompactPlus0672.small679,CompactPlus0672.nodes679,NodePlus10.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus0672.p680,GridPlus.atNode 680,GridPlus.atNode 681,NodePlus10.w40,CompactPlus0672.checked680,CompactPlus0672.small680,CompactPlus0672.nodes680,NodePlus10.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus0672.p681,GridPlus.atNode 681,GridPlus.atNode 682,NodePlus10.w41,CompactPlus0672.checked681,CompactPlus0672.small681,CompactPlus0672.nodes681,NodePlus10.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus0672.p682,GridPlus.atNode 682,GridPlus.atNode 683,NodePlus10.w42,CompactPlus0672.checked682,CompactPlus0672.small682,CompactPlus0672.nodes682,NodePlus10.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus0672.p683,GridPlus.atNode 683,GridPlus.atNode 684,NodePlus10.w43,CompactPlus0672.checked683,CompactPlus0672.small683,CompactPlus0672.nodes683,NodePlus10.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus0672.p684,GridPlus.atNode 684,GridPlus.atNode 685,NodePlus10.w44,CompactPlus0672.checked684,CompactPlus0672.small684,CompactPlus0672.nodes684,NodePlus10.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus0672.p685,GridPlus.atNode 685,GridPlus.atNode 686,NodePlus10.w45,CompactPlus0672.checked685,CompactPlus0672.small685,CompactPlus0672.nodes685,NodePlus10.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus0672.p686,GridPlus.atNode 686,GridPlus.atNode 687,NodePlus10.w46,CompactPlus0672.checked686,CompactPlus0672.small686,CompactPlus0672.nodes686,NodePlus10.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus0672.p687,GridPlus.atNode 687,GridPlus.atNode 688,NodePlus10.w47,CompactPlus0672.checked687,CompactPlus0672.small687,CompactPlus0672.nodes687,NodePlus10.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus0688.p688,GridPlus.atNode 688,GridPlus.atNode 689,NodePlus10.w48,CompactPlus0688.checked688,CompactPlus0688.small688,CompactPlus0688.nodes688,NodePlus10.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus0688.p689,GridPlus.atNode 689,GridPlus.atNode 690,NodePlus10.w49,CompactPlus0688.checked689,CompactPlus0688.small689,CompactPlus0688.nodes689,NodePlus10.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus0688.p690,GridPlus.atNode 690,GridPlus.atNode 691,NodePlus10.w50,CompactPlus0688.checked690,CompactPlus0688.small690,CompactPlus0688.nodes690,NodePlus10.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus0688.p691,GridPlus.atNode 691,GridPlus.atNode 692,NodePlus10.w51,CompactPlus0688.checked691,CompactPlus0688.small691,CompactPlus0688.nodes691,NodePlus10.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus0688.p692,GridPlus.atNode 692,GridPlus.atNode 693,NodePlus10.w52,CompactPlus0688.checked692,CompactPlus0688.small692,CompactPlus0688.nodes692,NodePlus10.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus0688.p693,GridPlus.atNode 693,GridPlus.atNode 694,NodePlus10.w53,CompactPlus0688.checked693,CompactPlus0688.small693,CompactPlus0688.nodes693,NodePlus10.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus0688.p694,GridPlus.atNode 694,GridPlus.atNode 695,NodePlus10.w54,CompactPlus0688.checked694,CompactPlus0688.small694,CompactPlus0688.nodes694,NodePlus10.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus0688.p695,GridPlus.atNode 695,GridPlus.atNode 696,NodePlus10.w55,CompactPlus0688.checked695,CompactPlus0688.small695,CompactPlus0688.nodes695,NodePlus10.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus0688.p696,GridPlus.atNode 696,GridPlus.atNode 697,NodePlus10.w56,CompactPlus0688.checked696,CompactPlus0688.small696,CompactPlus0688.nodes696,NodePlus10.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus0688.p697,GridPlus.atNode 697,GridPlus.atNode 698,NodePlus10.w57,CompactPlus0688.checked697,CompactPlus0688.small697,CompactPlus0688.nodes697,NodePlus10.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus0688.p698,GridPlus.atNode 698,GridPlus.atNode 699,NodePlus10.w58,CompactPlus0688.checked698,CompactPlus0688.small698,CompactPlus0688.nodes698,NodePlus10.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus0688.p699,GridPlus.atNode 699,GridPlus.atNode 700,NodePlus10.w59,CompactPlus0688.checked699,CompactPlus0688.small699,CompactPlus0688.nodes699,NodePlus10.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus0688.p700,GridPlus.atNode 700,GridPlus.atNode 701,NodePlus10.w60,CompactPlus0688.checked700,CompactPlus0688.small700,CompactPlus0688.nodes700,NodePlus10.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus0688.p701,GridPlus.atNode 701,GridPlus.atNode 702,NodePlus10.w61,CompactPlus0688.checked701,CompactPlus0688.small701,CompactPlus0688.nodes701,NodePlus10.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus0688.p702,GridPlus.atNode 702,GridPlus.atNode 703,NodePlus10.w62,CompactPlus0688.checked702,CompactPlus0688.small702,CompactPlus0688.nodes702,NodePlus10.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus0688.p703,GridPlus.atNode 703,GridPlus.atNode 704,NodePlus10.w63,CompactPlus0688.checked703,CompactPlus0688.small703,CompactPlus0688.nodes703,NodePlus10.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (640+j) ∧
    (atRow j).right=GridPlus.atNode (640+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus10
