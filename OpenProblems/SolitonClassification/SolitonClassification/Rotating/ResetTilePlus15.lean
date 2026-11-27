import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus0960
import SolitonClassification.Rotating.ResetPackedPlus0976
import SolitonClassification.Rotating.ResetPackedPlus0992
import SolitonClassification.Rotating.ResetPackedPlus1008
namespace SolitonClassification.Rotating.DyadicReset.TilePlus15
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus0960.p960,GridPlus.atNode 960,GridPlus.atNode 961,NodePlus15.w0,CompactPlus0960.checked960,CompactPlus0960.small960,CompactPlus0960.nodes960,NodePlus15.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus0960.p961,GridPlus.atNode 961,GridPlus.atNode 962,NodePlus15.w1,CompactPlus0960.checked961,CompactPlus0960.small961,CompactPlus0960.nodes961,NodePlus15.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus0960.p962,GridPlus.atNode 962,GridPlus.atNode 963,NodePlus15.w2,CompactPlus0960.checked962,CompactPlus0960.small962,CompactPlus0960.nodes962,NodePlus15.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus0960.p963,GridPlus.atNode 963,GridPlus.atNode 964,NodePlus15.w3,CompactPlus0960.checked963,CompactPlus0960.small963,CompactPlus0960.nodes963,NodePlus15.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus0960.p964,GridPlus.atNode 964,GridPlus.atNode 965,NodePlus15.w4,CompactPlus0960.checked964,CompactPlus0960.small964,CompactPlus0960.nodes964,NodePlus15.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus0960.p965,GridPlus.atNode 965,GridPlus.atNode 966,NodePlus15.w5,CompactPlus0960.checked965,CompactPlus0960.small965,CompactPlus0960.nodes965,NodePlus15.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus0960.p966,GridPlus.atNode 966,GridPlus.atNode 967,NodePlus15.w6,CompactPlus0960.checked966,CompactPlus0960.small966,CompactPlus0960.nodes966,NodePlus15.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus0960.p967,GridPlus.atNode 967,GridPlus.atNode 968,NodePlus15.w7,CompactPlus0960.checked967,CompactPlus0960.small967,CompactPlus0960.nodes967,NodePlus15.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus0960.p968,GridPlus.atNode 968,GridPlus.atNode 969,NodePlus15.w8,CompactPlus0960.checked968,CompactPlus0960.small968,CompactPlus0960.nodes968,NodePlus15.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus0960.p969,GridPlus.atNode 969,GridPlus.atNode 970,NodePlus15.w9,CompactPlus0960.checked969,CompactPlus0960.small969,CompactPlus0960.nodes969,NodePlus15.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus0960.p970,GridPlus.atNode 970,GridPlus.atNode 971,NodePlus15.w10,CompactPlus0960.checked970,CompactPlus0960.small970,CompactPlus0960.nodes970,NodePlus15.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus0960.p971,GridPlus.atNode 971,GridPlus.atNode 972,NodePlus15.w11,CompactPlus0960.checked971,CompactPlus0960.small971,CompactPlus0960.nodes971,NodePlus15.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus0960.p972,GridPlus.atNode 972,GridPlus.atNode 973,NodePlus15.w12,CompactPlus0960.checked972,CompactPlus0960.small972,CompactPlus0960.nodes972,NodePlus15.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus0960.p973,GridPlus.atNode 973,GridPlus.atNode 974,NodePlus15.w13,CompactPlus0960.checked973,CompactPlus0960.small973,CompactPlus0960.nodes973,NodePlus15.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus0960.p974,GridPlus.atNode 974,GridPlus.atNode 975,NodePlus15.w14,CompactPlus0960.checked974,CompactPlus0960.small974,CompactPlus0960.nodes974,NodePlus15.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus0960.p975,GridPlus.atNode 975,GridPlus.atNode 976,NodePlus15.w15,CompactPlus0960.checked975,CompactPlus0960.small975,CompactPlus0960.nodes975,NodePlus15.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus0976.p976,GridPlus.atNode 976,GridPlus.atNode 977,NodePlus15.w16,CompactPlus0976.checked976,CompactPlus0976.small976,CompactPlus0976.nodes976,NodePlus15.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus0976.p977,GridPlus.atNode 977,GridPlus.atNode 978,NodePlus15.w17,CompactPlus0976.checked977,CompactPlus0976.small977,CompactPlus0976.nodes977,NodePlus15.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus0976.p978,GridPlus.atNode 978,GridPlus.atNode 979,NodePlus15.w18,CompactPlus0976.checked978,CompactPlus0976.small978,CompactPlus0976.nodes978,NodePlus15.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus0976.p979,GridPlus.atNode 979,GridPlus.atNode 980,NodePlus15.w19,CompactPlus0976.checked979,CompactPlus0976.small979,CompactPlus0976.nodes979,NodePlus15.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus0976.p980,GridPlus.atNode 980,GridPlus.atNode 981,NodePlus15.w20,CompactPlus0976.checked980,CompactPlus0976.small980,CompactPlus0976.nodes980,NodePlus15.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus0976.p981,GridPlus.atNode 981,GridPlus.atNode 982,NodePlus15.w21,CompactPlus0976.checked981,CompactPlus0976.small981,CompactPlus0976.nodes981,NodePlus15.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus0976.p982,GridPlus.atNode 982,GridPlus.atNode 983,NodePlus15.w22,CompactPlus0976.checked982,CompactPlus0976.small982,CompactPlus0976.nodes982,NodePlus15.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus0976.p983,GridPlus.atNode 983,GridPlus.atNode 984,NodePlus15.w23,CompactPlus0976.checked983,CompactPlus0976.small983,CompactPlus0976.nodes983,NodePlus15.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus0976.p984,GridPlus.atNode 984,GridPlus.atNode 985,NodePlus15.w24,CompactPlus0976.checked984,CompactPlus0976.small984,CompactPlus0976.nodes984,NodePlus15.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus0976.p985,GridPlus.atNode 985,GridPlus.atNode 986,NodePlus15.w25,CompactPlus0976.checked985,CompactPlus0976.small985,CompactPlus0976.nodes985,NodePlus15.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus0976.p986,GridPlus.atNode 986,GridPlus.atNode 987,NodePlus15.w26,CompactPlus0976.checked986,CompactPlus0976.small986,CompactPlus0976.nodes986,NodePlus15.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus0976.p987,GridPlus.atNode 987,GridPlus.atNode 988,NodePlus15.w27,CompactPlus0976.checked987,CompactPlus0976.small987,CompactPlus0976.nodes987,NodePlus15.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus0976.p988,GridPlus.atNode 988,GridPlus.atNode 989,NodePlus15.w28,CompactPlus0976.checked988,CompactPlus0976.small988,CompactPlus0976.nodes988,NodePlus15.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus0976.p989,GridPlus.atNode 989,GridPlus.atNode 990,NodePlus15.w29,CompactPlus0976.checked989,CompactPlus0976.small989,CompactPlus0976.nodes989,NodePlus15.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus0976.p990,GridPlus.atNode 990,GridPlus.atNode 991,NodePlus15.w30,CompactPlus0976.checked990,CompactPlus0976.small990,CompactPlus0976.nodes990,NodePlus15.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus0976.p991,GridPlus.atNode 991,GridPlus.atNode 992,NodePlus15.w31,CompactPlus0976.checked991,CompactPlus0976.small991,CompactPlus0976.nodes991,NodePlus15.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus0992.p992,GridPlus.atNode 992,GridPlus.atNode 993,NodePlus15.w32,CompactPlus0992.checked992,CompactPlus0992.small992,CompactPlus0992.nodes992,NodePlus15.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus0992.p993,GridPlus.atNode 993,GridPlus.atNode 994,NodePlus15.w33,CompactPlus0992.checked993,CompactPlus0992.small993,CompactPlus0992.nodes993,NodePlus15.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus0992.p994,GridPlus.atNode 994,GridPlus.atNode 995,NodePlus15.w34,CompactPlus0992.checked994,CompactPlus0992.small994,CompactPlus0992.nodes994,NodePlus15.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus0992.p995,GridPlus.atNode 995,GridPlus.atNode 996,NodePlus15.w35,CompactPlus0992.checked995,CompactPlus0992.small995,CompactPlus0992.nodes995,NodePlus15.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus0992.p996,GridPlus.atNode 996,GridPlus.atNode 997,NodePlus15.w36,CompactPlus0992.checked996,CompactPlus0992.small996,CompactPlus0992.nodes996,NodePlus15.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus0992.p997,GridPlus.atNode 997,GridPlus.atNode 998,NodePlus15.w37,CompactPlus0992.checked997,CompactPlus0992.small997,CompactPlus0992.nodes997,NodePlus15.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus0992.p998,GridPlus.atNode 998,GridPlus.atNode 999,NodePlus15.w38,CompactPlus0992.checked998,CompactPlus0992.small998,CompactPlus0992.nodes998,NodePlus15.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus0992.p999,GridPlus.atNode 999,GridPlus.atNode 1000,NodePlus15.w39,CompactPlus0992.checked999,CompactPlus0992.small999,CompactPlus0992.nodes999,NodePlus15.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus0992.p1000,GridPlus.atNode 1000,GridPlus.atNode 1001,NodePlus15.w40,CompactPlus0992.checked1000,CompactPlus0992.small1000,CompactPlus0992.nodes1000,NodePlus15.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus0992.p1001,GridPlus.atNode 1001,GridPlus.atNode 1002,NodePlus15.w41,CompactPlus0992.checked1001,CompactPlus0992.small1001,CompactPlus0992.nodes1001,NodePlus15.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus0992.p1002,GridPlus.atNode 1002,GridPlus.atNode 1003,NodePlus15.w42,CompactPlus0992.checked1002,CompactPlus0992.small1002,CompactPlus0992.nodes1002,NodePlus15.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus0992.p1003,GridPlus.atNode 1003,GridPlus.atNode 1004,NodePlus15.w43,CompactPlus0992.checked1003,CompactPlus0992.small1003,CompactPlus0992.nodes1003,NodePlus15.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus0992.p1004,GridPlus.atNode 1004,GridPlus.atNode 1005,NodePlus15.w44,CompactPlus0992.checked1004,CompactPlus0992.small1004,CompactPlus0992.nodes1004,NodePlus15.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus0992.p1005,GridPlus.atNode 1005,GridPlus.atNode 1006,NodePlus15.w45,CompactPlus0992.checked1005,CompactPlus0992.small1005,CompactPlus0992.nodes1005,NodePlus15.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus0992.p1006,GridPlus.atNode 1006,GridPlus.atNode 1007,NodePlus15.w46,CompactPlus0992.checked1006,CompactPlus0992.small1006,CompactPlus0992.nodes1006,NodePlus15.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus0992.p1007,GridPlus.atNode 1007,GridPlus.atNode 1008,NodePlus15.w47,CompactPlus0992.checked1007,CompactPlus0992.small1007,CompactPlus0992.nodes1007,NodePlus15.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus1008.p1008,GridPlus.atNode 1008,GridPlus.atNode 1009,NodePlus15.w48,CompactPlus1008.checked1008,CompactPlus1008.small1008,CompactPlus1008.nodes1008,NodePlus15.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus1008.p1009,GridPlus.atNode 1009,GridPlus.atNode 1010,NodePlus15.w49,CompactPlus1008.checked1009,CompactPlus1008.small1009,CompactPlus1008.nodes1009,NodePlus15.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus1008.p1010,GridPlus.atNode 1010,GridPlus.atNode 1011,NodePlus15.w50,CompactPlus1008.checked1010,CompactPlus1008.small1010,CompactPlus1008.nodes1010,NodePlus15.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus1008.p1011,GridPlus.atNode 1011,GridPlus.atNode 1012,NodePlus15.w51,CompactPlus1008.checked1011,CompactPlus1008.small1011,CompactPlus1008.nodes1011,NodePlus15.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus1008.p1012,GridPlus.atNode 1012,GridPlus.atNode 1013,NodePlus15.w52,CompactPlus1008.checked1012,CompactPlus1008.small1012,CompactPlus1008.nodes1012,NodePlus15.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus1008.p1013,GridPlus.atNode 1013,GridPlus.atNode 1014,NodePlus15.w53,CompactPlus1008.checked1013,CompactPlus1008.small1013,CompactPlus1008.nodes1013,NodePlus15.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus1008.p1014,GridPlus.atNode 1014,GridPlus.atNode 1015,NodePlus15.w54,CompactPlus1008.checked1014,CompactPlus1008.small1014,CompactPlus1008.nodes1014,NodePlus15.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus1008.p1015,GridPlus.atNode 1015,GridPlus.atNode 1016,NodePlus15.w55,CompactPlus1008.checked1015,CompactPlus1008.small1015,CompactPlus1008.nodes1015,NodePlus15.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus1008.p1016,GridPlus.atNode 1016,GridPlus.atNode 1017,NodePlus15.w56,CompactPlus1008.checked1016,CompactPlus1008.small1016,CompactPlus1008.nodes1016,NodePlus15.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus1008.p1017,GridPlus.atNode 1017,GridPlus.atNode 1018,NodePlus15.w57,CompactPlus1008.checked1017,CompactPlus1008.small1017,CompactPlus1008.nodes1017,NodePlus15.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus1008.p1018,GridPlus.atNode 1018,GridPlus.atNode 1019,NodePlus15.w58,CompactPlus1008.checked1018,CompactPlus1008.small1018,CompactPlus1008.nodes1018,NodePlus15.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus1008.p1019,GridPlus.atNode 1019,GridPlus.atNode 1020,NodePlus15.w59,CompactPlus1008.checked1019,CompactPlus1008.small1019,CompactPlus1008.nodes1019,NodePlus15.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus1008.p1020,GridPlus.atNode 1020,GridPlus.atNode 1021,NodePlus15.w60,CompactPlus1008.checked1020,CompactPlus1008.small1020,CompactPlus1008.nodes1020,NodePlus15.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus1008.p1021,GridPlus.atNode 1021,GridPlus.atNode 1022,NodePlus15.w61,CompactPlus1008.checked1021,CompactPlus1008.small1021,CompactPlus1008.nodes1021,NodePlus15.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus1008.p1022,GridPlus.atNode 1022,GridPlus.atNode 1023,NodePlus15.w62,CompactPlus1008.checked1022,CompactPlus1008.small1022,CompactPlus1008.nodes1022,NodePlus15.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus1008.p1023,GridPlus.atNode 1023,GridPlus.atNode 1024,NodePlus15.w63,CompactPlus1008.checked1023,CompactPlus1008.small1023,CompactPlus1008.nodes1023,NodePlus15.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (960+j) ∧
    (atRow j).right=GridPlus.atNode (960+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus15
