import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus0640
import SolitonClassification.Rotating.ResetPackedMinus0656
import SolitonClassification.Rotating.ResetPackedMinus0672
import SolitonClassification.Rotating.ResetPackedMinus0688
namespace SolitonClassification.Rotating.DyadicReset.TileMinus10
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0640.p640,GridMinus.atNode 640,GridMinus.atNode 641,NodeMinus10.w0,CompactMinus0640.checked640,CompactMinus0640.small640,CompactMinus0640.nodes640,NodeMinus10.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0640.p641,GridMinus.atNode 641,GridMinus.atNode 642,NodeMinus10.w1,CompactMinus0640.checked641,CompactMinus0640.small641,CompactMinus0640.nodes641,NodeMinus10.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0640.p642,GridMinus.atNode 642,GridMinus.atNode 643,NodeMinus10.w2,CompactMinus0640.checked642,CompactMinus0640.small642,CompactMinus0640.nodes642,NodeMinus10.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0640.p643,GridMinus.atNode 643,GridMinus.atNode 644,NodeMinus10.w3,CompactMinus0640.checked643,CompactMinus0640.small643,CompactMinus0640.nodes643,NodeMinus10.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0640.p644,GridMinus.atNode 644,GridMinus.atNode 645,NodeMinus10.w4,CompactMinus0640.checked644,CompactMinus0640.small644,CompactMinus0640.nodes644,NodeMinus10.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0640.p645,GridMinus.atNode 645,GridMinus.atNode 646,NodeMinus10.w5,CompactMinus0640.checked645,CompactMinus0640.small645,CompactMinus0640.nodes645,NodeMinus10.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0640.p646,GridMinus.atNode 646,GridMinus.atNode 647,NodeMinus10.w6,CompactMinus0640.checked646,CompactMinus0640.small646,CompactMinus0640.nodes646,NodeMinus10.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0640.p647,GridMinus.atNode 647,GridMinus.atNode 648,NodeMinus10.w7,CompactMinus0640.checked647,CompactMinus0640.small647,CompactMinus0640.nodes647,NodeMinus10.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0640.p648,GridMinus.atNode 648,GridMinus.atNode 649,NodeMinus10.w8,CompactMinus0640.checked648,CompactMinus0640.small648,CompactMinus0640.nodes648,NodeMinus10.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0640.p649,GridMinus.atNode 649,GridMinus.atNode 650,NodeMinus10.w9,CompactMinus0640.checked649,CompactMinus0640.small649,CompactMinus0640.nodes649,NodeMinus10.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0640.p650,GridMinus.atNode 650,GridMinus.atNode 651,NodeMinus10.w10,CompactMinus0640.checked650,CompactMinus0640.small650,CompactMinus0640.nodes650,NodeMinus10.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0640.p651,GridMinus.atNode 651,GridMinus.atNode 652,NodeMinus10.w11,CompactMinus0640.checked651,CompactMinus0640.small651,CompactMinus0640.nodes651,NodeMinus10.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0640.p652,GridMinus.atNode 652,GridMinus.atNode 653,NodeMinus10.w12,CompactMinus0640.checked652,CompactMinus0640.small652,CompactMinus0640.nodes652,NodeMinus10.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0640.p653,GridMinus.atNode 653,GridMinus.atNode 654,NodeMinus10.w13,CompactMinus0640.checked653,CompactMinus0640.small653,CompactMinus0640.nodes653,NodeMinus10.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0640.p654,GridMinus.atNode 654,GridMinus.atNode 655,NodeMinus10.w14,CompactMinus0640.checked654,CompactMinus0640.small654,CompactMinus0640.nodes654,NodeMinus10.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0640.p655,GridMinus.atNode 655,GridMinus.atNode 656,NodeMinus10.w15,CompactMinus0640.checked655,CompactMinus0640.small655,CompactMinus0640.nodes655,NodeMinus10.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0656.p656,GridMinus.atNode 656,GridMinus.atNode 657,NodeMinus10.w16,CompactMinus0656.checked656,CompactMinus0656.small656,CompactMinus0656.nodes656,NodeMinus10.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0656.p657,GridMinus.atNode 657,GridMinus.atNode 658,NodeMinus10.w17,CompactMinus0656.checked657,CompactMinus0656.small657,CompactMinus0656.nodes657,NodeMinus10.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0656.p658,GridMinus.atNode 658,GridMinus.atNode 659,NodeMinus10.w18,CompactMinus0656.checked658,CompactMinus0656.small658,CompactMinus0656.nodes658,NodeMinus10.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0656.p659,GridMinus.atNode 659,GridMinus.atNode 660,NodeMinus10.w19,CompactMinus0656.checked659,CompactMinus0656.small659,CompactMinus0656.nodes659,NodeMinus10.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0656.p660,GridMinus.atNode 660,GridMinus.atNode 661,NodeMinus10.w20,CompactMinus0656.checked660,CompactMinus0656.small660,CompactMinus0656.nodes660,NodeMinus10.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0656.p661,GridMinus.atNode 661,GridMinus.atNode 662,NodeMinus10.w21,CompactMinus0656.checked661,CompactMinus0656.small661,CompactMinus0656.nodes661,NodeMinus10.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0656.p662,GridMinus.atNode 662,GridMinus.atNode 663,NodeMinus10.w22,CompactMinus0656.checked662,CompactMinus0656.small662,CompactMinus0656.nodes662,NodeMinus10.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0656.p663,GridMinus.atNode 663,GridMinus.atNode 664,NodeMinus10.w23,CompactMinus0656.checked663,CompactMinus0656.small663,CompactMinus0656.nodes663,NodeMinus10.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0656.p664,GridMinus.atNode 664,GridMinus.atNode 665,NodeMinus10.w24,CompactMinus0656.checked664,CompactMinus0656.small664,CompactMinus0656.nodes664,NodeMinus10.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0656.p665,GridMinus.atNode 665,GridMinus.atNode 666,NodeMinus10.w25,CompactMinus0656.checked665,CompactMinus0656.small665,CompactMinus0656.nodes665,NodeMinus10.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0656.p666,GridMinus.atNode 666,GridMinus.atNode 667,NodeMinus10.w26,CompactMinus0656.checked666,CompactMinus0656.small666,CompactMinus0656.nodes666,NodeMinus10.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0656.p667,GridMinus.atNode 667,GridMinus.atNode 668,NodeMinus10.w27,CompactMinus0656.checked667,CompactMinus0656.small667,CompactMinus0656.nodes667,NodeMinus10.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0656.p668,GridMinus.atNode 668,GridMinus.atNode 669,NodeMinus10.w28,CompactMinus0656.checked668,CompactMinus0656.small668,CompactMinus0656.nodes668,NodeMinus10.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0656.p669,GridMinus.atNode 669,GridMinus.atNode 670,NodeMinus10.w29,CompactMinus0656.checked669,CompactMinus0656.small669,CompactMinus0656.nodes669,NodeMinus10.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0656.p670,GridMinus.atNode 670,GridMinus.atNode 671,NodeMinus10.w30,CompactMinus0656.checked670,CompactMinus0656.small670,CompactMinus0656.nodes670,NodeMinus10.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0656.p671,GridMinus.atNode 671,GridMinus.atNode 672,NodeMinus10.w31,CompactMinus0656.checked671,CompactMinus0656.small671,CompactMinus0656.nodes671,NodeMinus10.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0672.p672,GridMinus.atNode 672,GridMinus.atNode 673,NodeMinus10.w32,CompactMinus0672.checked672,CompactMinus0672.small672,CompactMinus0672.nodes672,NodeMinus10.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0672.p673,GridMinus.atNode 673,GridMinus.atNode 674,NodeMinus10.w33,CompactMinus0672.checked673,CompactMinus0672.small673,CompactMinus0672.nodes673,NodeMinus10.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0672.p674,GridMinus.atNode 674,GridMinus.atNode 675,NodeMinus10.w34,CompactMinus0672.checked674,CompactMinus0672.small674,CompactMinus0672.nodes674,NodeMinus10.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0672.p675,GridMinus.atNode 675,GridMinus.atNode 676,NodeMinus10.w35,CompactMinus0672.checked675,CompactMinus0672.small675,CompactMinus0672.nodes675,NodeMinus10.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0672.p676,GridMinus.atNode 676,GridMinus.atNode 677,NodeMinus10.w36,CompactMinus0672.checked676,CompactMinus0672.small676,CompactMinus0672.nodes676,NodeMinus10.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0672.p677,GridMinus.atNode 677,GridMinus.atNode 678,NodeMinus10.w37,CompactMinus0672.checked677,CompactMinus0672.small677,CompactMinus0672.nodes677,NodeMinus10.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0672.p678,GridMinus.atNode 678,GridMinus.atNode 679,NodeMinus10.w38,CompactMinus0672.checked678,CompactMinus0672.small678,CompactMinus0672.nodes678,NodeMinus10.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0672.p679,GridMinus.atNode 679,GridMinus.atNode 680,NodeMinus10.w39,CompactMinus0672.checked679,CompactMinus0672.small679,CompactMinus0672.nodes679,NodeMinus10.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0672.p680,GridMinus.atNode 680,GridMinus.atNode 681,NodeMinus10.w40,CompactMinus0672.checked680,CompactMinus0672.small680,CompactMinus0672.nodes680,NodeMinus10.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0672.p681,GridMinus.atNode 681,GridMinus.atNode 682,NodeMinus10.w41,CompactMinus0672.checked681,CompactMinus0672.small681,CompactMinus0672.nodes681,NodeMinus10.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0672.p682,GridMinus.atNode 682,GridMinus.atNode 683,NodeMinus10.w42,CompactMinus0672.checked682,CompactMinus0672.small682,CompactMinus0672.nodes682,NodeMinus10.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0672.p683,GridMinus.atNode 683,GridMinus.atNode 684,NodeMinus10.w43,CompactMinus0672.checked683,CompactMinus0672.small683,CompactMinus0672.nodes683,NodeMinus10.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0672.p684,GridMinus.atNode 684,GridMinus.atNode 685,NodeMinus10.w44,CompactMinus0672.checked684,CompactMinus0672.small684,CompactMinus0672.nodes684,NodeMinus10.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0672.p685,GridMinus.atNode 685,GridMinus.atNode 686,NodeMinus10.w45,CompactMinus0672.checked685,CompactMinus0672.small685,CompactMinus0672.nodes685,NodeMinus10.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0672.p686,GridMinus.atNode 686,GridMinus.atNode 687,NodeMinus10.w46,CompactMinus0672.checked686,CompactMinus0672.small686,CompactMinus0672.nodes686,NodeMinus10.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0672.p687,GridMinus.atNode 687,GridMinus.atNode 688,NodeMinus10.w47,CompactMinus0672.checked687,CompactMinus0672.small687,CompactMinus0672.nodes687,NodeMinus10.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0688.p688,GridMinus.atNode 688,GridMinus.atNode 689,NodeMinus10.w48,CompactMinus0688.checked688,CompactMinus0688.small688,CompactMinus0688.nodes688,NodeMinus10.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0688.p689,GridMinus.atNode 689,GridMinus.atNode 690,NodeMinus10.w49,CompactMinus0688.checked689,CompactMinus0688.small689,CompactMinus0688.nodes689,NodeMinus10.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0688.p690,GridMinus.atNode 690,GridMinus.atNode 691,NodeMinus10.w50,CompactMinus0688.checked690,CompactMinus0688.small690,CompactMinus0688.nodes690,NodeMinus10.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0688.p691,GridMinus.atNode 691,GridMinus.atNode 692,NodeMinus10.w51,CompactMinus0688.checked691,CompactMinus0688.small691,CompactMinus0688.nodes691,NodeMinus10.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0688.p692,GridMinus.atNode 692,GridMinus.atNode 693,NodeMinus10.w52,CompactMinus0688.checked692,CompactMinus0688.small692,CompactMinus0688.nodes692,NodeMinus10.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0688.p693,GridMinus.atNode 693,GridMinus.atNode 694,NodeMinus10.w53,CompactMinus0688.checked693,CompactMinus0688.small693,CompactMinus0688.nodes693,NodeMinus10.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0688.p694,GridMinus.atNode 694,GridMinus.atNode 695,NodeMinus10.w54,CompactMinus0688.checked694,CompactMinus0688.small694,CompactMinus0688.nodes694,NodeMinus10.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0688.p695,GridMinus.atNode 695,GridMinus.atNode 696,NodeMinus10.w55,CompactMinus0688.checked695,CompactMinus0688.small695,CompactMinus0688.nodes695,NodeMinus10.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0688.p696,GridMinus.atNode 696,GridMinus.atNode 697,NodeMinus10.w56,CompactMinus0688.checked696,CompactMinus0688.small696,CompactMinus0688.nodes696,NodeMinus10.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0688.p697,GridMinus.atNode 697,GridMinus.atNode 698,NodeMinus10.w57,CompactMinus0688.checked697,CompactMinus0688.small697,CompactMinus0688.nodes697,NodeMinus10.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0688.p698,GridMinus.atNode 698,GridMinus.atNode 699,NodeMinus10.w58,CompactMinus0688.checked698,CompactMinus0688.small698,CompactMinus0688.nodes698,NodeMinus10.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0688.p699,GridMinus.atNode 699,GridMinus.atNode 700,NodeMinus10.w59,CompactMinus0688.checked699,CompactMinus0688.small699,CompactMinus0688.nodes699,NodeMinus10.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0688.p700,GridMinus.atNode 700,GridMinus.atNode 701,NodeMinus10.w60,CompactMinus0688.checked700,CompactMinus0688.small700,CompactMinus0688.nodes700,NodeMinus10.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0688.p701,GridMinus.atNode 701,GridMinus.atNode 702,NodeMinus10.w61,CompactMinus0688.checked701,CompactMinus0688.small701,CompactMinus0688.nodes701,NodeMinus10.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0688.p702,GridMinus.atNode 702,GridMinus.atNode 703,NodeMinus10.w62,CompactMinus0688.checked702,CompactMinus0688.small702,CompactMinus0688.nodes702,NodeMinus10.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0688.p703,GridMinus.atNode 703,GridMinus.atNode 704,NodeMinus10.w63,CompactMinus0688.checked703,CompactMinus0688.small703,CompactMinus0688.nodes703,NodeMinus10.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (640+j) ∧
    (atRow j).right=GridMinus.atNode (640+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus10
