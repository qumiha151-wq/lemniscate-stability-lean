import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus0832
import SolitonClassification.Rotating.ResetPackedMinus0848
import SolitonClassification.Rotating.ResetPackedMinus0864
import SolitonClassification.Rotating.ResetPackedMinus0880
namespace SolitonClassification.Rotating.DyadicReset.TileMinus13
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0832.p832,GridMinus.atNode 832,GridMinus.atNode 833,NodeMinus13.w0,CompactMinus0832.checked832,CompactMinus0832.small832,CompactMinus0832.nodes832,NodeMinus13.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0832.p833,GridMinus.atNode 833,GridMinus.atNode 834,NodeMinus13.w1,CompactMinus0832.checked833,CompactMinus0832.small833,CompactMinus0832.nodes833,NodeMinus13.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0832.p834,GridMinus.atNode 834,GridMinus.atNode 835,NodeMinus13.w2,CompactMinus0832.checked834,CompactMinus0832.small834,CompactMinus0832.nodes834,NodeMinus13.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0832.p835,GridMinus.atNode 835,GridMinus.atNode 836,NodeMinus13.w3,CompactMinus0832.checked835,CompactMinus0832.small835,CompactMinus0832.nodes835,NodeMinus13.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0832.p836,GridMinus.atNode 836,GridMinus.atNode 837,NodeMinus13.w4,CompactMinus0832.checked836,CompactMinus0832.small836,CompactMinus0832.nodes836,NodeMinus13.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0832.p837,GridMinus.atNode 837,GridMinus.atNode 838,NodeMinus13.w5,CompactMinus0832.checked837,CompactMinus0832.small837,CompactMinus0832.nodes837,NodeMinus13.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0832.p838,GridMinus.atNode 838,GridMinus.atNode 839,NodeMinus13.w6,CompactMinus0832.checked838,CompactMinus0832.small838,CompactMinus0832.nodes838,NodeMinus13.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0832.p839,GridMinus.atNode 839,GridMinus.atNode 840,NodeMinus13.w7,CompactMinus0832.checked839,CompactMinus0832.small839,CompactMinus0832.nodes839,NodeMinus13.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0832.p840,GridMinus.atNode 840,GridMinus.atNode 841,NodeMinus13.w8,CompactMinus0832.checked840,CompactMinus0832.small840,CompactMinus0832.nodes840,NodeMinus13.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0832.p841,GridMinus.atNode 841,GridMinus.atNode 842,NodeMinus13.w9,CompactMinus0832.checked841,CompactMinus0832.small841,CompactMinus0832.nodes841,NodeMinus13.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0832.p842,GridMinus.atNode 842,GridMinus.atNode 843,NodeMinus13.w10,CompactMinus0832.checked842,CompactMinus0832.small842,CompactMinus0832.nodes842,NodeMinus13.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0832.p843,GridMinus.atNode 843,GridMinus.atNode 844,NodeMinus13.w11,CompactMinus0832.checked843,CompactMinus0832.small843,CompactMinus0832.nodes843,NodeMinus13.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0832.p844,GridMinus.atNode 844,GridMinus.atNode 845,NodeMinus13.w12,CompactMinus0832.checked844,CompactMinus0832.small844,CompactMinus0832.nodes844,NodeMinus13.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0832.p845,GridMinus.atNode 845,GridMinus.atNode 846,NodeMinus13.w13,CompactMinus0832.checked845,CompactMinus0832.small845,CompactMinus0832.nodes845,NodeMinus13.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0832.p846,GridMinus.atNode 846,GridMinus.atNode 847,NodeMinus13.w14,CompactMinus0832.checked846,CompactMinus0832.small846,CompactMinus0832.nodes846,NodeMinus13.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0832.p847,GridMinus.atNode 847,GridMinus.atNode 848,NodeMinus13.w15,CompactMinus0832.checked847,CompactMinus0832.small847,CompactMinus0832.nodes847,NodeMinus13.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0848.p848,GridMinus.atNode 848,GridMinus.atNode 849,NodeMinus13.w16,CompactMinus0848.checked848,CompactMinus0848.small848,CompactMinus0848.nodes848,NodeMinus13.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0848.p849,GridMinus.atNode 849,GridMinus.atNode 850,NodeMinus13.w17,CompactMinus0848.checked849,CompactMinus0848.small849,CompactMinus0848.nodes849,NodeMinus13.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0848.p850,GridMinus.atNode 850,GridMinus.atNode 851,NodeMinus13.w18,CompactMinus0848.checked850,CompactMinus0848.small850,CompactMinus0848.nodes850,NodeMinus13.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0848.p851,GridMinus.atNode 851,GridMinus.atNode 852,NodeMinus13.w19,CompactMinus0848.checked851,CompactMinus0848.small851,CompactMinus0848.nodes851,NodeMinus13.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0848.p852,GridMinus.atNode 852,GridMinus.atNode 853,NodeMinus13.w20,CompactMinus0848.checked852,CompactMinus0848.small852,CompactMinus0848.nodes852,NodeMinus13.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0848.p853,GridMinus.atNode 853,GridMinus.atNode 854,NodeMinus13.w21,CompactMinus0848.checked853,CompactMinus0848.small853,CompactMinus0848.nodes853,NodeMinus13.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0848.p854,GridMinus.atNode 854,GridMinus.atNode 855,NodeMinus13.w22,CompactMinus0848.checked854,CompactMinus0848.small854,CompactMinus0848.nodes854,NodeMinus13.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0848.p855,GridMinus.atNode 855,GridMinus.atNode 856,NodeMinus13.w23,CompactMinus0848.checked855,CompactMinus0848.small855,CompactMinus0848.nodes855,NodeMinus13.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0848.p856,GridMinus.atNode 856,GridMinus.atNode 857,NodeMinus13.w24,CompactMinus0848.checked856,CompactMinus0848.small856,CompactMinus0848.nodes856,NodeMinus13.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0848.p857,GridMinus.atNode 857,GridMinus.atNode 858,NodeMinus13.w25,CompactMinus0848.checked857,CompactMinus0848.small857,CompactMinus0848.nodes857,NodeMinus13.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0848.p858,GridMinus.atNode 858,GridMinus.atNode 859,NodeMinus13.w26,CompactMinus0848.checked858,CompactMinus0848.small858,CompactMinus0848.nodes858,NodeMinus13.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0848.p859,GridMinus.atNode 859,GridMinus.atNode 860,NodeMinus13.w27,CompactMinus0848.checked859,CompactMinus0848.small859,CompactMinus0848.nodes859,NodeMinus13.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0848.p860,GridMinus.atNode 860,GridMinus.atNode 861,NodeMinus13.w28,CompactMinus0848.checked860,CompactMinus0848.small860,CompactMinus0848.nodes860,NodeMinus13.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0848.p861,GridMinus.atNode 861,GridMinus.atNode 862,NodeMinus13.w29,CompactMinus0848.checked861,CompactMinus0848.small861,CompactMinus0848.nodes861,NodeMinus13.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0848.p862,GridMinus.atNode 862,GridMinus.atNode 863,NodeMinus13.w30,CompactMinus0848.checked862,CompactMinus0848.small862,CompactMinus0848.nodes862,NodeMinus13.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0848.p863,GridMinus.atNode 863,GridMinus.atNode 864,NodeMinus13.w31,CompactMinus0848.checked863,CompactMinus0848.small863,CompactMinus0848.nodes863,NodeMinus13.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0864.p864,GridMinus.atNode 864,GridMinus.atNode 865,NodeMinus13.w32,CompactMinus0864.checked864,CompactMinus0864.small864,CompactMinus0864.nodes864,NodeMinus13.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0864.p865,GridMinus.atNode 865,GridMinus.atNode 866,NodeMinus13.w33,CompactMinus0864.checked865,CompactMinus0864.small865,CompactMinus0864.nodes865,NodeMinus13.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0864.p866,GridMinus.atNode 866,GridMinus.atNode 867,NodeMinus13.w34,CompactMinus0864.checked866,CompactMinus0864.small866,CompactMinus0864.nodes866,NodeMinus13.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0864.p867,GridMinus.atNode 867,GridMinus.atNode 868,NodeMinus13.w35,CompactMinus0864.checked867,CompactMinus0864.small867,CompactMinus0864.nodes867,NodeMinus13.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0864.p868,GridMinus.atNode 868,GridMinus.atNode 869,NodeMinus13.w36,CompactMinus0864.checked868,CompactMinus0864.small868,CompactMinus0864.nodes868,NodeMinus13.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0864.p869,GridMinus.atNode 869,GridMinus.atNode 870,NodeMinus13.w37,CompactMinus0864.checked869,CompactMinus0864.small869,CompactMinus0864.nodes869,NodeMinus13.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0864.p870,GridMinus.atNode 870,GridMinus.atNode 871,NodeMinus13.w38,CompactMinus0864.checked870,CompactMinus0864.small870,CompactMinus0864.nodes870,NodeMinus13.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0864.p871,GridMinus.atNode 871,GridMinus.atNode 872,NodeMinus13.w39,CompactMinus0864.checked871,CompactMinus0864.small871,CompactMinus0864.nodes871,NodeMinus13.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0864.p872,GridMinus.atNode 872,GridMinus.atNode 873,NodeMinus13.w40,CompactMinus0864.checked872,CompactMinus0864.small872,CompactMinus0864.nodes872,NodeMinus13.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0864.p873,GridMinus.atNode 873,GridMinus.atNode 874,NodeMinus13.w41,CompactMinus0864.checked873,CompactMinus0864.small873,CompactMinus0864.nodes873,NodeMinus13.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0864.p874,GridMinus.atNode 874,GridMinus.atNode 875,NodeMinus13.w42,CompactMinus0864.checked874,CompactMinus0864.small874,CompactMinus0864.nodes874,NodeMinus13.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0864.p875,GridMinus.atNode 875,GridMinus.atNode 876,NodeMinus13.w43,CompactMinus0864.checked875,CompactMinus0864.small875,CompactMinus0864.nodes875,NodeMinus13.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0864.p876,GridMinus.atNode 876,GridMinus.atNode 877,NodeMinus13.w44,CompactMinus0864.checked876,CompactMinus0864.small876,CompactMinus0864.nodes876,NodeMinus13.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0864.p877,GridMinus.atNode 877,GridMinus.atNode 878,NodeMinus13.w45,CompactMinus0864.checked877,CompactMinus0864.small877,CompactMinus0864.nodes877,NodeMinus13.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0864.p878,GridMinus.atNode 878,GridMinus.atNode 879,NodeMinus13.w46,CompactMinus0864.checked878,CompactMinus0864.small878,CompactMinus0864.nodes878,NodeMinus13.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0864.p879,GridMinus.atNode 879,GridMinus.atNode 880,NodeMinus13.w47,CompactMinus0864.checked879,CompactMinus0864.small879,CompactMinus0864.nodes879,NodeMinus13.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0880.p880,GridMinus.atNode 880,GridMinus.atNode 881,NodeMinus13.w48,CompactMinus0880.checked880,CompactMinus0880.small880,CompactMinus0880.nodes880,NodeMinus13.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0880.p881,GridMinus.atNode 881,GridMinus.atNode 882,NodeMinus13.w49,CompactMinus0880.checked881,CompactMinus0880.small881,CompactMinus0880.nodes881,NodeMinus13.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0880.p882,GridMinus.atNode 882,GridMinus.atNode 883,NodeMinus13.w50,CompactMinus0880.checked882,CompactMinus0880.small882,CompactMinus0880.nodes882,NodeMinus13.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0880.p883,GridMinus.atNode 883,GridMinus.atNode 884,NodeMinus13.w51,CompactMinus0880.checked883,CompactMinus0880.small883,CompactMinus0880.nodes883,NodeMinus13.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0880.p884,GridMinus.atNode 884,GridMinus.atNode 885,NodeMinus13.w52,CompactMinus0880.checked884,CompactMinus0880.small884,CompactMinus0880.nodes884,NodeMinus13.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0880.p885,GridMinus.atNode 885,GridMinus.atNode 886,NodeMinus13.w53,CompactMinus0880.checked885,CompactMinus0880.small885,CompactMinus0880.nodes885,NodeMinus13.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0880.p886,GridMinus.atNode 886,GridMinus.atNode 887,NodeMinus13.w54,CompactMinus0880.checked886,CompactMinus0880.small886,CompactMinus0880.nodes886,NodeMinus13.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0880.p887,GridMinus.atNode 887,GridMinus.atNode 888,NodeMinus13.w55,CompactMinus0880.checked887,CompactMinus0880.small887,CompactMinus0880.nodes887,NodeMinus13.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0880.p888,GridMinus.atNode 888,GridMinus.atNode 889,NodeMinus13.w56,CompactMinus0880.checked888,CompactMinus0880.small888,CompactMinus0880.nodes888,NodeMinus13.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0880.p889,GridMinus.atNode 889,GridMinus.atNode 890,NodeMinus13.w57,CompactMinus0880.checked889,CompactMinus0880.small889,CompactMinus0880.nodes889,NodeMinus13.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0880.p890,GridMinus.atNode 890,GridMinus.atNode 891,NodeMinus13.w58,CompactMinus0880.checked890,CompactMinus0880.small890,CompactMinus0880.nodes890,NodeMinus13.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0880.p891,GridMinus.atNode 891,GridMinus.atNode 892,NodeMinus13.w59,CompactMinus0880.checked891,CompactMinus0880.small891,CompactMinus0880.nodes891,NodeMinus13.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0880.p892,GridMinus.atNode 892,GridMinus.atNode 893,NodeMinus13.w60,CompactMinus0880.checked892,CompactMinus0880.small892,CompactMinus0880.nodes892,NodeMinus13.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0880.p893,GridMinus.atNode 893,GridMinus.atNode 894,NodeMinus13.w61,CompactMinus0880.checked893,CompactMinus0880.small893,CompactMinus0880.nodes893,NodeMinus13.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0880.p894,GridMinus.atNode 894,GridMinus.atNode 895,NodeMinus13.w62,CompactMinus0880.checked894,CompactMinus0880.small894,CompactMinus0880.nodes894,NodeMinus13.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0880.p895,GridMinus.atNode 895,GridMinus.atNode 896,NodeMinus13.w63,CompactMinus0880.checked895,CompactMinus0880.small895,CompactMinus0880.nodes895,NodeMinus13.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (832+j) ∧
    (atRow j).right=GridMinus.atNode (832+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus13
