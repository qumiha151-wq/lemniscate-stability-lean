import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus0832
import SolitonClassification.Rotating.ResetPackedPlus0848
import SolitonClassification.Rotating.ResetPackedPlus0864
import SolitonClassification.Rotating.ResetPackedPlus0880
namespace SolitonClassification.Rotating.DyadicReset.TilePlus13
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus0832.p832,GridPlus.atNode 832,GridPlus.atNode 833,NodePlus13.w0,CompactPlus0832.checked832,CompactPlus0832.small832,CompactPlus0832.nodes832,NodePlus13.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus0832.p833,GridPlus.atNode 833,GridPlus.atNode 834,NodePlus13.w1,CompactPlus0832.checked833,CompactPlus0832.small833,CompactPlus0832.nodes833,NodePlus13.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus0832.p834,GridPlus.atNode 834,GridPlus.atNode 835,NodePlus13.w2,CompactPlus0832.checked834,CompactPlus0832.small834,CompactPlus0832.nodes834,NodePlus13.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus0832.p835,GridPlus.atNode 835,GridPlus.atNode 836,NodePlus13.w3,CompactPlus0832.checked835,CompactPlus0832.small835,CompactPlus0832.nodes835,NodePlus13.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus0832.p836,GridPlus.atNode 836,GridPlus.atNode 837,NodePlus13.w4,CompactPlus0832.checked836,CompactPlus0832.small836,CompactPlus0832.nodes836,NodePlus13.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus0832.p837,GridPlus.atNode 837,GridPlus.atNode 838,NodePlus13.w5,CompactPlus0832.checked837,CompactPlus0832.small837,CompactPlus0832.nodes837,NodePlus13.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus0832.p838,GridPlus.atNode 838,GridPlus.atNode 839,NodePlus13.w6,CompactPlus0832.checked838,CompactPlus0832.small838,CompactPlus0832.nodes838,NodePlus13.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus0832.p839,GridPlus.atNode 839,GridPlus.atNode 840,NodePlus13.w7,CompactPlus0832.checked839,CompactPlus0832.small839,CompactPlus0832.nodes839,NodePlus13.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus0832.p840,GridPlus.atNode 840,GridPlus.atNode 841,NodePlus13.w8,CompactPlus0832.checked840,CompactPlus0832.small840,CompactPlus0832.nodes840,NodePlus13.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus0832.p841,GridPlus.atNode 841,GridPlus.atNode 842,NodePlus13.w9,CompactPlus0832.checked841,CompactPlus0832.small841,CompactPlus0832.nodes841,NodePlus13.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus0832.p842,GridPlus.atNode 842,GridPlus.atNode 843,NodePlus13.w10,CompactPlus0832.checked842,CompactPlus0832.small842,CompactPlus0832.nodes842,NodePlus13.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus0832.p843,GridPlus.atNode 843,GridPlus.atNode 844,NodePlus13.w11,CompactPlus0832.checked843,CompactPlus0832.small843,CompactPlus0832.nodes843,NodePlus13.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus0832.p844,GridPlus.atNode 844,GridPlus.atNode 845,NodePlus13.w12,CompactPlus0832.checked844,CompactPlus0832.small844,CompactPlus0832.nodes844,NodePlus13.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus0832.p845,GridPlus.atNode 845,GridPlus.atNode 846,NodePlus13.w13,CompactPlus0832.checked845,CompactPlus0832.small845,CompactPlus0832.nodes845,NodePlus13.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus0832.p846,GridPlus.atNode 846,GridPlus.atNode 847,NodePlus13.w14,CompactPlus0832.checked846,CompactPlus0832.small846,CompactPlus0832.nodes846,NodePlus13.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus0832.p847,GridPlus.atNode 847,GridPlus.atNode 848,NodePlus13.w15,CompactPlus0832.checked847,CompactPlus0832.small847,CompactPlus0832.nodes847,NodePlus13.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus0848.p848,GridPlus.atNode 848,GridPlus.atNode 849,NodePlus13.w16,CompactPlus0848.checked848,CompactPlus0848.small848,CompactPlus0848.nodes848,NodePlus13.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus0848.p849,GridPlus.atNode 849,GridPlus.atNode 850,NodePlus13.w17,CompactPlus0848.checked849,CompactPlus0848.small849,CompactPlus0848.nodes849,NodePlus13.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus0848.p850,GridPlus.atNode 850,GridPlus.atNode 851,NodePlus13.w18,CompactPlus0848.checked850,CompactPlus0848.small850,CompactPlus0848.nodes850,NodePlus13.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus0848.p851,GridPlus.atNode 851,GridPlus.atNode 852,NodePlus13.w19,CompactPlus0848.checked851,CompactPlus0848.small851,CompactPlus0848.nodes851,NodePlus13.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus0848.p852,GridPlus.atNode 852,GridPlus.atNode 853,NodePlus13.w20,CompactPlus0848.checked852,CompactPlus0848.small852,CompactPlus0848.nodes852,NodePlus13.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus0848.p853,GridPlus.atNode 853,GridPlus.atNode 854,NodePlus13.w21,CompactPlus0848.checked853,CompactPlus0848.small853,CompactPlus0848.nodes853,NodePlus13.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus0848.p854,GridPlus.atNode 854,GridPlus.atNode 855,NodePlus13.w22,CompactPlus0848.checked854,CompactPlus0848.small854,CompactPlus0848.nodes854,NodePlus13.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus0848.p855,GridPlus.atNode 855,GridPlus.atNode 856,NodePlus13.w23,CompactPlus0848.checked855,CompactPlus0848.small855,CompactPlus0848.nodes855,NodePlus13.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus0848.p856,GridPlus.atNode 856,GridPlus.atNode 857,NodePlus13.w24,CompactPlus0848.checked856,CompactPlus0848.small856,CompactPlus0848.nodes856,NodePlus13.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus0848.p857,GridPlus.atNode 857,GridPlus.atNode 858,NodePlus13.w25,CompactPlus0848.checked857,CompactPlus0848.small857,CompactPlus0848.nodes857,NodePlus13.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus0848.p858,GridPlus.atNode 858,GridPlus.atNode 859,NodePlus13.w26,CompactPlus0848.checked858,CompactPlus0848.small858,CompactPlus0848.nodes858,NodePlus13.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus0848.p859,GridPlus.atNode 859,GridPlus.atNode 860,NodePlus13.w27,CompactPlus0848.checked859,CompactPlus0848.small859,CompactPlus0848.nodes859,NodePlus13.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus0848.p860,GridPlus.atNode 860,GridPlus.atNode 861,NodePlus13.w28,CompactPlus0848.checked860,CompactPlus0848.small860,CompactPlus0848.nodes860,NodePlus13.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus0848.p861,GridPlus.atNode 861,GridPlus.atNode 862,NodePlus13.w29,CompactPlus0848.checked861,CompactPlus0848.small861,CompactPlus0848.nodes861,NodePlus13.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus0848.p862,GridPlus.atNode 862,GridPlus.atNode 863,NodePlus13.w30,CompactPlus0848.checked862,CompactPlus0848.small862,CompactPlus0848.nodes862,NodePlus13.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus0848.p863,GridPlus.atNode 863,GridPlus.atNode 864,NodePlus13.w31,CompactPlus0848.checked863,CompactPlus0848.small863,CompactPlus0848.nodes863,NodePlus13.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus0864.p864,GridPlus.atNode 864,GridPlus.atNode 865,NodePlus13.w32,CompactPlus0864.checked864,CompactPlus0864.small864,CompactPlus0864.nodes864,NodePlus13.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus0864.p865,GridPlus.atNode 865,GridPlus.atNode 866,NodePlus13.w33,CompactPlus0864.checked865,CompactPlus0864.small865,CompactPlus0864.nodes865,NodePlus13.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus0864.p866,GridPlus.atNode 866,GridPlus.atNode 867,NodePlus13.w34,CompactPlus0864.checked866,CompactPlus0864.small866,CompactPlus0864.nodes866,NodePlus13.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus0864.p867,GridPlus.atNode 867,GridPlus.atNode 868,NodePlus13.w35,CompactPlus0864.checked867,CompactPlus0864.small867,CompactPlus0864.nodes867,NodePlus13.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus0864.p868,GridPlus.atNode 868,GridPlus.atNode 869,NodePlus13.w36,CompactPlus0864.checked868,CompactPlus0864.small868,CompactPlus0864.nodes868,NodePlus13.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus0864.p869,GridPlus.atNode 869,GridPlus.atNode 870,NodePlus13.w37,CompactPlus0864.checked869,CompactPlus0864.small869,CompactPlus0864.nodes869,NodePlus13.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus0864.p870,GridPlus.atNode 870,GridPlus.atNode 871,NodePlus13.w38,CompactPlus0864.checked870,CompactPlus0864.small870,CompactPlus0864.nodes870,NodePlus13.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus0864.p871,GridPlus.atNode 871,GridPlus.atNode 872,NodePlus13.w39,CompactPlus0864.checked871,CompactPlus0864.small871,CompactPlus0864.nodes871,NodePlus13.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus0864.p872,GridPlus.atNode 872,GridPlus.atNode 873,NodePlus13.w40,CompactPlus0864.checked872,CompactPlus0864.small872,CompactPlus0864.nodes872,NodePlus13.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus0864.p873,GridPlus.atNode 873,GridPlus.atNode 874,NodePlus13.w41,CompactPlus0864.checked873,CompactPlus0864.small873,CompactPlus0864.nodes873,NodePlus13.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus0864.p874,GridPlus.atNode 874,GridPlus.atNode 875,NodePlus13.w42,CompactPlus0864.checked874,CompactPlus0864.small874,CompactPlus0864.nodes874,NodePlus13.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus0864.p875,GridPlus.atNode 875,GridPlus.atNode 876,NodePlus13.w43,CompactPlus0864.checked875,CompactPlus0864.small875,CompactPlus0864.nodes875,NodePlus13.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus0864.p876,GridPlus.atNode 876,GridPlus.atNode 877,NodePlus13.w44,CompactPlus0864.checked876,CompactPlus0864.small876,CompactPlus0864.nodes876,NodePlus13.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus0864.p877,GridPlus.atNode 877,GridPlus.atNode 878,NodePlus13.w45,CompactPlus0864.checked877,CompactPlus0864.small877,CompactPlus0864.nodes877,NodePlus13.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus0864.p878,GridPlus.atNode 878,GridPlus.atNode 879,NodePlus13.w46,CompactPlus0864.checked878,CompactPlus0864.small878,CompactPlus0864.nodes878,NodePlus13.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus0864.p879,GridPlus.atNode 879,GridPlus.atNode 880,NodePlus13.w47,CompactPlus0864.checked879,CompactPlus0864.small879,CompactPlus0864.nodes879,NodePlus13.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus0880.p880,GridPlus.atNode 880,GridPlus.atNode 881,NodePlus13.w48,CompactPlus0880.checked880,CompactPlus0880.small880,CompactPlus0880.nodes880,NodePlus13.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus0880.p881,GridPlus.atNode 881,GridPlus.atNode 882,NodePlus13.w49,CompactPlus0880.checked881,CompactPlus0880.small881,CompactPlus0880.nodes881,NodePlus13.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus0880.p882,GridPlus.atNode 882,GridPlus.atNode 883,NodePlus13.w50,CompactPlus0880.checked882,CompactPlus0880.small882,CompactPlus0880.nodes882,NodePlus13.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus0880.p883,GridPlus.atNode 883,GridPlus.atNode 884,NodePlus13.w51,CompactPlus0880.checked883,CompactPlus0880.small883,CompactPlus0880.nodes883,NodePlus13.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus0880.p884,GridPlus.atNode 884,GridPlus.atNode 885,NodePlus13.w52,CompactPlus0880.checked884,CompactPlus0880.small884,CompactPlus0880.nodes884,NodePlus13.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus0880.p885,GridPlus.atNode 885,GridPlus.atNode 886,NodePlus13.w53,CompactPlus0880.checked885,CompactPlus0880.small885,CompactPlus0880.nodes885,NodePlus13.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus0880.p886,GridPlus.atNode 886,GridPlus.atNode 887,NodePlus13.w54,CompactPlus0880.checked886,CompactPlus0880.small886,CompactPlus0880.nodes886,NodePlus13.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus0880.p887,GridPlus.atNode 887,GridPlus.atNode 888,NodePlus13.w55,CompactPlus0880.checked887,CompactPlus0880.small887,CompactPlus0880.nodes887,NodePlus13.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus0880.p888,GridPlus.atNode 888,GridPlus.atNode 889,NodePlus13.w56,CompactPlus0880.checked888,CompactPlus0880.small888,CompactPlus0880.nodes888,NodePlus13.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus0880.p889,GridPlus.atNode 889,GridPlus.atNode 890,NodePlus13.w57,CompactPlus0880.checked889,CompactPlus0880.small889,CompactPlus0880.nodes889,NodePlus13.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus0880.p890,GridPlus.atNode 890,GridPlus.atNode 891,NodePlus13.w58,CompactPlus0880.checked890,CompactPlus0880.small890,CompactPlus0880.nodes890,NodePlus13.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus0880.p891,GridPlus.atNode 891,GridPlus.atNode 892,NodePlus13.w59,CompactPlus0880.checked891,CompactPlus0880.small891,CompactPlus0880.nodes891,NodePlus13.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus0880.p892,GridPlus.atNode 892,GridPlus.atNode 893,NodePlus13.w60,CompactPlus0880.checked892,CompactPlus0880.small892,CompactPlus0880.nodes892,NodePlus13.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus0880.p893,GridPlus.atNode 893,GridPlus.atNode 894,NodePlus13.w61,CompactPlus0880.checked893,CompactPlus0880.small893,CompactPlus0880.nodes893,NodePlus13.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus0880.p894,GridPlus.atNode 894,GridPlus.atNode 895,NodePlus13.w62,CompactPlus0880.checked894,CompactPlus0880.small894,CompactPlus0880.nodes894,NodePlus13.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus0880.p895,GridPlus.atNode 895,GridPlus.atNode 896,NodePlus13.w63,CompactPlus0880.checked895,CompactPlus0880.small895,CompactPlus0880.nodes895,NodePlus13.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (832+j) ∧
    (atRow j).right=GridPlus.atNode (832+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus13
