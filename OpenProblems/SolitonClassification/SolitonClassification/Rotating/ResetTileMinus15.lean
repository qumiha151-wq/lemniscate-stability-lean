import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus0960
import SolitonClassification.Rotating.ResetPackedMinus0976
import SolitonClassification.Rotating.ResetPackedMinus0992
import SolitonClassification.Rotating.ResetPackedMinus1008
namespace SolitonClassification.Rotating.DyadicReset.TileMinus15
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0960.p960,GridMinus.atNode 960,GridMinus.atNode 961,NodeMinus15.w0,CompactMinus0960.checked960,CompactMinus0960.small960,CompactMinus0960.nodes960,NodeMinus15.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0960.p961,GridMinus.atNode 961,GridMinus.atNode 962,NodeMinus15.w1,CompactMinus0960.checked961,CompactMinus0960.small961,CompactMinus0960.nodes961,NodeMinus15.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0960.p962,GridMinus.atNode 962,GridMinus.atNode 963,NodeMinus15.w2,CompactMinus0960.checked962,CompactMinus0960.small962,CompactMinus0960.nodes962,NodeMinus15.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0960.p963,GridMinus.atNode 963,GridMinus.atNode 964,NodeMinus15.w3,CompactMinus0960.checked963,CompactMinus0960.small963,CompactMinus0960.nodes963,NodeMinus15.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0960.p964,GridMinus.atNode 964,GridMinus.atNode 965,NodeMinus15.w4,CompactMinus0960.checked964,CompactMinus0960.small964,CompactMinus0960.nodes964,NodeMinus15.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0960.p965,GridMinus.atNode 965,GridMinus.atNode 966,NodeMinus15.w5,CompactMinus0960.checked965,CompactMinus0960.small965,CompactMinus0960.nodes965,NodeMinus15.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0960.p966,GridMinus.atNode 966,GridMinus.atNode 967,NodeMinus15.w6,CompactMinus0960.checked966,CompactMinus0960.small966,CompactMinus0960.nodes966,NodeMinus15.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0960.p967,GridMinus.atNode 967,GridMinus.atNode 968,NodeMinus15.w7,CompactMinus0960.checked967,CompactMinus0960.small967,CompactMinus0960.nodes967,NodeMinus15.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0960.p968,GridMinus.atNode 968,GridMinus.atNode 969,NodeMinus15.w8,CompactMinus0960.checked968,CompactMinus0960.small968,CompactMinus0960.nodes968,NodeMinus15.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0960.p969,GridMinus.atNode 969,GridMinus.atNode 970,NodeMinus15.w9,CompactMinus0960.checked969,CompactMinus0960.small969,CompactMinus0960.nodes969,NodeMinus15.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0960.p970,GridMinus.atNode 970,GridMinus.atNode 971,NodeMinus15.w10,CompactMinus0960.checked970,CompactMinus0960.small970,CompactMinus0960.nodes970,NodeMinus15.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0960.p971,GridMinus.atNode 971,GridMinus.atNode 972,NodeMinus15.w11,CompactMinus0960.checked971,CompactMinus0960.small971,CompactMinus0960.nodes971,NodeMinus15.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0960.p972,GridMinus.atNode 972,GridMinus.atNode 973,NodeMinus15.w12,CompactMinus0960.checked972,CompactMinus0960.small972,CompactMinus0960.nodes972,NodeMinus15.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0960.p973,GridMinus.atNode 973,GridMinus.atNode 974,NodeMinus15.w13,CompactMinus0960.checked973,CompactMinus0960.small973,CompactMinus0960.nodes973,NodeMinus15.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0960.p974,GridMinus.atNode 974,GridMinus.atNode 975,NodeMinus15.w14,CompactMinus0960.checked974,CompactMinus0960.small974,CompactMinus0960.nodes974,NodeMinus15.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0960.p975,GridMinus.atNode 975,GridMinus.atNode 976,NodeMinus15.w15,CompactMinus0960.checked975,CompactMinus0960.small975,CompactMinus0960.nodes975,NodeMinus15.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0976.p976,GridMinus.atNode 976,GridMinus.atNode 977,NodeMinus15.w16,CompactMinus0976.checked976,CompactMinus0976.small976,CompactMinus0976.nodes976,NodeMinus15.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0976.p977,GridMinus.atNode 977,GridMinus.atNode 978,NodeMinus15.w17,CompactMinus0976.checked977,CompactMinus0976.small977,CompactMinus0976.nodes977,NodeMinus15.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0976.p978,GridMinus.atNode 978,GridMinus.atNode 979,NodeMinus15.w18,CompactMinus0976.checked978,CompactMinus0976.small978,CompactMinus0976.nodes978,NodeMinus15.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0976.p979,GridMinus.atNode 979,GridMinus.atNode 980,NodeMinus15.w19,CompactMinus0976.checked979,CompactMinus0976.small979,CompactMinus0976.nodes979,NodeMinus15.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0976.p980,GridMinus.atNode 980,GridMinus.atNode 981,NodeMinus15.w20,CompactMinus0976.checked980,CompactMinus0976.small980,CompactMinus0976.nodes980,NodeMinus15.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0976.p981,GridMinus.atNode 981,GridMinus.atNode 982,NodeMinus15.w21,CompactMinus0976.checked981,CompactMinus0976.small981,CompactMinus0976.nodes981,NodeMinus15.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0976.p982,GridMinus.atNode 982,GridMinus.atNode 983,NodeMinus15.w22,CompactMinus0976.checked982,CompactMinus0976.small982,CompactMinus0976.nodes982,NodeMinus15.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0976.p983,GridMinus.atNode 983,GridMinus.atNode 984,NodeMinus15.w23,CompactMinus0976.checked983,CompactMinus0976.small983,CompactMinus0976.nodes983,NodeMinus15.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0976.p984,GridMinus.atNode 984,GridMinus.atNode 985,NodeMinus15.w24,CompactMinus0976.checked984,CompactMinus0976.small984,CompactMinus0976.nodes984,NodeMinus15.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0976.p985,GridMinus.atNode 985,GridMinus.atNode 986,NodeMinus15.w25,CompactMinus0976.checked985,CompactMinus0976.small985,CompactMinus0976.nodes985,NodeMinus15.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0976.p986,GridMinus.atNode 986,GridMinus.atNode 987,NodeMinus15.w26,CompactMinus0976.checked986,CompactMinus0976.small986,CompactMinus0976.nodes986,NodeMinus15.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0976.p987,GridMinus.atNode 987,GridMinus.atNode 988,NodeMinus15.w27,CompactMinus0976.checked987,CompactMinus0976.small987,CompactMinus0976.nodes987,NodeMinus15.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0976.p988,GridMinus.atNode 988,GridMinus.atNode 989,NodeMinus15.w28,CompactMinus0976.checked988,CompactMinus0976.small988,CompactMinus0976.nodes988,NodeMinus15.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0976.p989,GridMinus.atNode 989,GridMinus.atNode 990,NodeMinus15.w29,CompactMinus0976.checked989,CompactMinus0976.small989,CompactMinus0976.nodes989,NodeMinus15.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0976.p990,GridMinus.atNode 990,GridMinus.atNode 991,NodeMinus15.w30,CompactMinus0976.checked990,CompactMinus0976.small990,CompactMinus0976.nodes990,NodeMinus15.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0976.p991,GridMinus.atNode 991,GridMinus.atNode 992,NodeMinus15.w31,CompactMinus0976.checked991,CompactMinus0976.small991,CompactMinus0976.nodes991,NodeMinus15.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0992.p992,GridMinus.atNode 992,GridMinus.atNode 993,NodeMinus15.w32,CompactMinus0992.checked992,CompactMinus0992.small992,CompactMinus0992.nodes992,NodeMinus15.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0992.p993,GridMinus.atNode 993,GridMinus.atNode 994,NodeMinus15.w33,CompactMinus0992.checked993,CompactMinus0992.small993,CompactMinus0992.nodes993,NodeMinus15.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0992.p994,GridMinus.atNode 994,GridMinus.atNode 995,NodeMinus15.w34,CompactMinus0992.checked994,CompactMinus0992.small994,CompactMinus0992.nodes994,NodeMinus15.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0992.p995,GridMinus.atNode 995,GridMinus.atNode 996,NodeMinus15.w35,CompactMinus0992.checked995,CompactMinus0992.small995,CompactMinus0992.nodes995,NodeMinus15.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0992.p996,GridMinus.atNode 996,GridMinus.atNode 997,NodeMinus15.w36,CompactMinus0992.checked996,CompactMinus0992.small996,CompactMinus0992.nodes996,NodeMinus15.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0992.p997,GridMinus.atNode 997,GridMinus.atNode 998,NodeMinus15.w37,CompactMinus0992.checked997,CompactMinus0992.small997,CompactMinus0992.nodes997,NodeMinus15.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0992.p998,GridMinus.atNode 998,GridMinus.atNode 999,NodeMinus15.w38,CompactMinus0992.checked998,CompactMinus0992.small998,CompactMinus0992.nodes998,NodeMinus15.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0992.p999,GridMinus.atNode 999,GridMinus.atNode 1000,NodeMinus15.w39,CompactMinus0992.checked999,CompactMinus0992.small999,CompactMinus0992.nodes999,NodeMinus15.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0992.p1000,GridMinus.atNode 1000,GridMinus.atNode 1001,NodeMinus15.w40,CompactMinus0992.checked1000,CompactMinus0992.small1000,CompactMinus0992.nodes1000,NodeMinus15.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0992.p1001,GridMinus.atNode 1001,GridMinus.atNode 1002,NodeMinus15.w41,CompactMinus0992.checked1001,CompactMinus0992.small1001,CompactMinus0992.nodes1001,NodeMinus15.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0992.p1002,GridMinus.atNode 1002,GridMinus.atNode 1003,NodeMinus15.w42,CompactMinus0992.checked1002,CompactMinus0992.small1002,CompactMinus0992.nodes1002,NodeMinus15.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0992.p1003,GridMinus.atNode 1003,GridMinus.atNode 1004,NodeMinus15.w43,CompactMinus0992.checked1003,CompactMinus0992.small1003,CompactMinus0992.nodes1003,NodeMinus15.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0992.p1004,GridMinus.atNode 1004,GridMinus.atNode 1005,NodeMinus15.w44,CompactMinus0992.checked1004,CompactMinus0992.small1004,CompactMinus0992.nodes1004,NodeMinus15.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0992.p1005,GridMinus.atNode 1005,GridMinus.atNode 1006,NodeMinus15.w45,CompactMinus0992.checked1005,CompactMinus0992.small1005,CompactMinus0992.nodes1005,NodeMinus15.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0992.p1006,GridMinus.atNode 1006,GridMinus.atNode 1007,NodeMinus15.w46,CompactMinus0992.checked1006,CompactMinus0992.small1006,CompactMinus0992.nodes1006,NodeMinus15.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus0992.p1007,GridMinus.atNode 1007,GridMinus.atNode 1008,NodeMinus15.w47,CompactMinus0992.checked1007,CompactMinus0992.small1007,CompactMinus0992.nodes1007,NodeMinus15.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1008.p1008,GridMinus.atNode 1008,GridMinus.atNode 1009,NodeMinus15.w48,CompactMinus1008.checked1008,CompactMinus1008.small1008,CompactMinus1008.nodes1008,NodeMinus15.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1008.p1009,GridMinus.atNode 1009,GridMinus.atNode 1010,NodeMinus15.w49,CompactMinus1008.checked1009,CompactMinus1008.small1009,CompactMinus1008.nodes1009,NodeMinus15.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1008.p1010,GridMinus.atNode 1010,GridMinus.atNode 1011,NodeMinus15.w50,CompactMinus1008.checked1010,CompactMinus1008.small1010,CompactMinus1008.nodes1010,NodeMinus15.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1008.p1011,GridMinus.atNode 1011,GridMinus.atNode 1012,NodeMinus15.w51,CompactMinus1008.checked1011,CompactMinus1008.small1011,CompactMinus1008.nodes1011,NodeMinus15.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1008.p1012,GridMinus.atNode 1012,GridMinus.atNode 1013,NodeMinus15.w52,CompactMinus1008.checked1012,CompactMinus1008.small1012,CompactMinus1008.nodes1012,NodeMinus15.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1008.p1013,GridMinus.atNode 1013,GridMinus.atNode 1014,NodeMinus15.w53,CompactMinus1008.checked1013,CompactMinus1008.small1013,CompactMinus1008.nodes1013,NodeMinus15.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1008.p1014,GridMinus.atNode 1014,GridMinus.atNode 1015,NodeMinus15.w54,CompactMinus1008.checked1014,CompactMinus1008.small1014,CompactMinus1008.nodes1014,NodeMinus15.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1008.p1015,GridMinus.atNode 1015,GridMinus.atNode 1016,NodeMinus15.w55,CompactMinus1008.checked1015,CompactMinus1008.small1015,CompactMinus1008.nodes1015,NodeMinus15.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1008.p1016,GridMinus.atNode 1016,GridMinus.atNode 1017,NodeMinus15.w56,CompactMinus1008.checked1016,CompactMinus1008.small1016,CompactMinus1008.nodes1016,NodeMinus15.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1008.p1017,GridMinus.atNode 1017,GridMinus.atNode 1018,NodeMinus15.w57,CompactMinus1008.checked1017,CompactMinus1008.small1017,CompactMinus1008.nodes1017,NodeMinus15.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1008.p1018,GridMinus.atNode 1018,GridMinus.atNode 1019,NodeMinus15.w58,CompactMinus1008.checked1018,CompactMinus1008.small1018,CompactMinus1008.nodes1018,NodeMinus15.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1008.p1019,GridMinus.atNode 1019,GridMinus.atNode 1020,NodeMinus15.w59,CompactMinus1008.checked1019,CompactMinus1008.small1019,CompactMinus1008.nodes1019,NodeMinus15.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1008.p1020,GridMinus.atNode 1020,GridMinus.atNode 1021,NodeMinus15.w60,CompactMinus1008.checked1020,CompactMinus1008.small1020,CompactMinus1008.nodes1020,NodeMinus15.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1008.p1021,GridMinus.atNode 1021,GridMinus.atNode 1022,NodeMinus15.w61,CompactMinus1008.checked1021,CompactMinus1008.small1021,CompactMinus1008.nodes1021,NodeMinus15.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1008.p1022,GridMinus.atNode 1022,GridMinus.atNode 1023,NodeMinus15.w62,CompactMinus1008.checked1022,CompactMinus1008.small1022,CompactMinus1008.nodes1022,NodeMinus15.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1008.p1023,GridMinus.atNode 1023,GridMinus.atNode 1024,NodeMinus15.w63,CompactMinus1008.checked1023,CompactMinus1008.small1023,CompactMinus1008.nodes1023,NodeMinus15.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (960+j) ∧
    (atRow j).right=GridMinus.atNode (960+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus15
