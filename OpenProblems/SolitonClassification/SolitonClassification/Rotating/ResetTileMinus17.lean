import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus1088
import SolitonClassification.Rotating.ResetPackedMinus1104
import SolitonClassification.Rotating.ResetPackedMinus1120
import SolitonClassification.Rotating.ResetPackedMinus1136
namespace SolitonClassification.Rotating.DyadicReset.TileMinus17
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1088.p1088,GridMinus.atNode 1088,GridMinus.atNode 1089,NodeMinus17.w0,CompactMinus1088.checked1088,CompactMinus1088.small1088,CompactMinus1088.nodes1088,NodeMinus17.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1088.p1089,GridMinus.atNode 1089,GridMinus.atNode 1090,NodeMinus17.w1,CompactMinus1088.checked1089,CompactMinus1088.small1089,CompactMinus1088.nodes1089,NodeMinus17.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1088.p1090,GridMinus.atNode 1090,GridMinus.atNode 1091,NodeMinus17.w2,CompactMinus1088.checked1090,CompactMinus1088.small1090,CompactMinus1088.nodes1090,NodeMinus17.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1088.p1091,GridMinus.atNode 1091,GridMinus.atNode 1092,NodeMinus17.w3,CompactMinus1088.checked1091,CompactMinus1088.small1091,CompactMinus1088.nodes1091,NodeMinus17.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1088.p1092,GridMinus.atNode 1092,GridMinus.atNode 1093,NodeMinus17.w4,CompactMinus1088.checked1092,CompactMinus1088.small1092,CompactMinus1088.nodes1092,NodeMinus17.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1088.p1093,GridMinus.atNode 1093,GridMinus.atNode 1094,NodeMinus17.w5,CompactMinus1088.checked1093,CompactMinus1088.small1093,CompactMinus1088.nodes1093,NodeMinus17.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1088.p1094,GridMinus.atNode 1094,GridMinus.atNode 1095,NodeMinus17.w6,CompactMinus1088.checked1094,CompactMinus1088.small1094,CompactMinus1088.nodes1094,NodeMinus17.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1088.p1095,GridMinus.atNode 1095,GridMinus.atNode 1096,NodeMinus17.w7,CompactMinus1088.checked1095,CompactMinus1088.small1095,CompactMinus1088.nodes1095,NodeMinus17.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1088.p1096,GridMinus.atNode 1096,GridMinus.atNode 1097,NodeMinus17.w8,CompactMinus1088.checked1096,CompactMinus1088.small1096,CompactMinus1088.nodes1096,NodeMinus17.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1088.p1097,GridMinus.atNode 1097,GridMinus.atNode 1098,NodeMinus17.w9,CompactMinus1088.checked1097,CompactMinus1088.small1097,CompactMinus1088.nodes1097,NodeMinus17.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1088.p1098,GridMinus.atNode 1098,GridMinus.atNode 1099,NodeMinus17.w10,CompactMinus1088.checked1098,CompactMinus1088.small1098,CompactMinus1088.nodes1098,NodeMinus17.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1088.p1099,GridMinus.atNode 1099,GridMinus.atNode 1100,NodeMinus17.w11,CompactMinus1088.checked1099,CompactMinus1088.small1099,CompactMinus1088.nodes1099,NodeMinus17.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1088.p1100,GridMinus.atNode 1100,GridMinus.atNode 1101,NodeMinus17.w12,CompactMinus1088.checked1100,CompactMinus1088.small1100,CompactMinus1088.nodes1100,NodeMinus17.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1088.p1101,GridMinus.atNode 1101,GridMinus.atNode 1102,NodeMinus17.w13,CompactMinus1088.checked1101,CompactMinus1088.small1101,CompactMinus1088.nodes1101,NodeMinus17.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1088.p1102,GridMinus.atNode 1102,GridMinus.atNode 1103,NodeMinus17.w14,CompactMinus1088.checked1102,CompactMinus1088.small1102,CompactMinus1088.nodes1102,NodeMinus17.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1088.p1103,GridMinus.atNode 1103,GridMinus.atNode 1104,NodeMinus17.w15,CompactMinus1088.checked1103,CompactMinus1088.small1103,CompactMinus1088.nodes1103,NodeMinus17.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1104.p1104,GridMinus.atNode 1104,GridMinus.atNode 1105,NodeMinus17.w16,CompactMinus1104.checked1104,CompactMinus1104.small1104,CompactMinus1104.nodes1104,NodeMinus17.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1104.p1105,GridMinus.atNode 1105,GridMinus.atNode 1106,NodeMinus17.w17,CompactMinus1104.checked1105,CompactMinus1104.small1105,CompactMinus1104.nodes1105,NodeMinus17.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1104.p1106,GridMinus.atNode 1106,GridMinus.atNode 1107,NodeMinus17.w18,CompactMinus1104.checked1106,CompactMinus1104.small1106,CompactMinus1104.nodes1106,NodeMinus17.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1104.p1107,GridMinus.atNode 1107,GridMinus.atNode 1108,NodeMinus17.w19,CompactMinus1104.checked1107,CompactMinus1104.small1107,CompactMinus1104.nodes1107,NodeMinus17.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1104.p1108,GridMinus.atNode 1108,GridMinus.atNode 1109,NodeMinus17.w20,CompactMinus1104.checked1108,CompactMinus1104.small1108,CompactMinus1104.nodes1108,NodeMinus17.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1104.p1109,GridMinus.atNode 1109,GridMinus.atNode 1110,NodeMinus17.w21,CompactMinus1104.checked1109,CompactMinus1104.small1109,CompactMinus1104.nodes1109,NodeMinus17.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1104.p1110,GridMinus.atNode 1110,GridMinus.atNode 1111,NodeMinus17.w22,CompactMinus1104.checked1110,CompactMinus1104.small1110,CompactMinus1104.nodes1110,NodeMinus17.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1104.p1111,GridMinus.atNode 1111,GridMinus.atNode 1112,NodeMinus17.w23,CompactMinus1104.checked1111,CompactMinus1104.small1111,CompactMinus1104.nodes1111,NodeMinus17.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1104.p1112,GridMinus.atNode 1112,GridMinus.atNode 1113,NodeMinus17.w24,CompactMinus1104.checked1112,CompactMinus1104.small1112,CompactMinus1104.nodes1112,NodeMinus17.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1104.p1113,GridMinus.atNode 1113,GridMinus.atNode 1114,NodeMinus17.w25,CompactMinus1104.checked1113,CompactMinus1104.small1113,CompactMinus1104.nodes1113,NodeMinus17.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1104.p1114,GridMinus.atNode 1114,GridMinus.atNode 1115,NodeMinus17.w26,CompactMinus1104.checked1114,CompactMinus1104.small1114,CompactMinus1104.nodes1114,NodeMinus17.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1104.p1115,GridMinus.atNode 1115,GridMinus.atNode 1116,NodeMinus17.w27,CompactMinus1104.checked1115,CompactMinus1104.small1115,CompactMinus1104.nodes1115,NodeMinus17.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1104.p1116,GridMinus.atNode 1116,GridMinus.atNode 1117,NodeMinus17.w28,CompactMinus1104.checked1116,CompactMinus1104.small1116,CompactMinus1104.nodes1116,NodeMinus17.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1104.p1117,GridMinus.atNode 1117,GridMinus.atNode 1118,NodeMinus17.w29,CompactMinus1104.checked1117,CompactMinus1104.small1117,CompactMinus1104.nodes1117,NodeMinus17.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1104.p1118,GridMinus.atNode 1118,GridMinus.atNode 1119,NodeMinus17.w30,CompactMinus1104.checked1118,CompactMinus1104.small1118,CompactMinus1104.nodes1118,NodeMinus17.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1104.p1119,GridMinus.atNode 1119,GridMinus.atNode 1120,NodeMinus17.w31,CompactMinus1104.checked1119,CompactMinus1104.small1119,CompactMinus1104.nodes1119,NodeMinus17.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1120.p1120,GridMinus.atNode 1120,GridMinus.atNode 1121,NodeMinus17.w32,CompactMinus1120.checked1120,CompactMinus1120.small1120,CompactMinus1120.nodes1120,NodeMinus17.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1120.p1121,GridMinus.atNode 1121,GridMinus.atNode 1122,NodeMinus17.w33,CompactMinus1120.checked1121,CompactMinus1120.small1121,CompactMinus1120.nodes1121,NodeMinus17.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1120.p1122,GridMinus.atNode 1122,GridMinus.atNode 1123,NodeMinus17.w34,CompactMinus1120.checked1122,CompactMinus1120.small1122,CompactMinus1120.nodes1122,NodeMinus17.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1120.p1123,GridMinus.atNode 1123,GridMinus.atNode 1124,NodeMinus17.w35,CompactMinus1120.checked1123,CompactMinus1120.small1123,CompactMinus1120.nodes1123,NodeMinus17.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1120.p1124,GridMinus.atNode 1124,GridMinus.atNode 1125,NodeMinus17.w36,CompactMinus1120.checked1124,CompactMinus1120.small1124,CompactMinus1120.nodes1124,NodeMinus17.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1120.p1125,GridMinus.atNode 1125,GridMinus.atNode 1126,NodeMinus17.w37,CompactMinus1120.checked1125,CompactMinus1120.small1125,CompactMinus1120.nodes1125,NodeMinus17.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1120.p1126,GridMinus.atNode 1126,GridMinus.atNode 1127,NodeMinus17.w38,CompactMinus1120.checked1126,CompactMinus1120.small1126,CompactMinus1120.nodes1126,NodeMinus17.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1120.p1127,GridMinus.atNode 1127,GridMinus.atNode 1128,NodeMinus17.w39,CompactMinus1120.checked1127,CompactMinus1120.small1127,CompactMinus1120.nodes1127,NodeMinus17.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1120.p1128,GridMinus.atNode 1128,GridMinus.atNode 1129,NodeMinus17.w40,CompactMinus1120.checked1128,CompactMinus1120.small1128,CompactMinus1120.nodes1128,NodeMinus17.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1120.p1129,GridMinus.atNode 1129,GridMinus.atNode 1130,NodeMinus17.w41,CompactMinus1120.checked1129,CompactMinus1120.small1129,CompactMinus1120.nodes1129,NodeMinus17.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1120.p1130,GridMinus.atNode 1130,GridMinus.atNode 1131,NodeMinus17.w42,CompactMinus1120.checked1130,CompactMinus1120.small1130,CompactMinus1120.nodes1130,NodeMinus17.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1120.p1131,GridMinus.atNode 1131,GridMinus.atNode 1132,NodeMinus17.w43,CompactMinus1120.checked1131,CompactMinus1120.small1131,CompactMinus1120.nodes1131,NodeMinus17.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1120.p1132,GridMinus.atNode 1132,GridMinus.atNode 1133,NodeMinus17.w44,CompactMinus1120.checked1132,CompactMinus1120.small1132,CompactMinus1120.nodes1132,NodeMinus17.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1120.p1133,GridMinus.atNode 1133,GridMinus.atNode 1134,NodeMinus17.w45,CompactMinus1120.checked1133,CompactMinus1120.small1133,CompactMinus1120.nodes1133,NodeMinus17.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1120.p1134,GridMinus.atNode 1134,GridMinus.atNode 1135,NodeMinus17.w46,CompactMinus1120.checked1134,CompactMinus1120.small1134,CompactMinus1120.nodes1134,NodeMinus17.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1120.p1135,GridMinus.atNode 1135,GridMinus.atNode 1136,NodeMinus17.w47,CompactMinus1120.checked1135,CompactMinus1120.small1135,CompactMinus1120.nodes1135,NodeMinus17.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1136.p1136,GridMinus.atNode 1136,GridMinus.atNode 1137,NodeMinus17.w48,CompactMinus1136.checked1136,CompactMinus1136.small1136,CompactMinus1136.nodes1136,NodeMinus17.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1136.p1137,GridMinus.atNode 1137,GridMinus.atNode 1138,NodeMinus17.w49,CompactMinus1136.checked1137,CompactMinus1136.small1137,CompactMinus1136.nodes1137,NodeMinus17.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1136.p1138,GridMinus.atNode 1138,GridMinus.atNode 1139,NodeMinus17.w50,CompactMinus1136.checked1138,CompactMinus1136.small1138,CompactMinus1136.nodes1138,NodeMinus17.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1136.p1139,GridMinus.atNode 1139,GridMinus.atNode 1140,NodeMinus17.w51,CompactMinus1136.checked1139,CompactMinus1136.small1139,CompactMinus1136.nodes1139,NodeMinus17.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1136.p1140,GridMinus.atNode 1140,GridMinus.atNode 1141,NodeMinus17.w52,CompactMinus1136.checked1140,CompactMinus1136.small1140,CompactMinus1136.nodes1140,NodeMinus17.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1136.p1141,GridMinus.atNode 1141,GridMinus.atNode 1142,NodeMinus17.w53,CompactMinus1136.checked1141,CompactMinus1136.small1141,CompactMinus1136.nodes1141,NodeMinus17.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1136.p1142,GridMinus.atNode 1142,GridMinus.atNode 1143,NodeMinus17.w54,CompactMinus1136.checked1142,CompactMinus1136.small1142,CompactMinus1136.nodes1142,NodeMinus17.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1136.p1143,GridMinus.atNode 1143,GridMinus.atNode 1144,NodeMinus17.w55,CompactMinus1136.checked1143,CompactMinus1136.small1143,CompactMinus1136.nodes1143,NodeMinus17.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1136.p1144,GridMinus.atNode 1144,GridMinus.atNode 1145,NodeMinus17.w56,CompactMinus1136.checked1144,CompactMinus1136.small1144,CompactMinus1136.nodes1144,NodeMinus17.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1136.p1145,GridMinus.atNode 1145,GridMinus.atNode 1146,NodeMinus17.w57,CompactMinus1136.checked1145,CompactMinus1136.small1145,CompactMinus1136.nodes1145,NodeMinus17.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1136.p1146,GridMinus.atNode 1146,GridMinus.atNode 1147,NodeMinus17.w58,CompactMinus1136.checked1146,CompactMinus1136.small1146,CompactMinus1136.nodes1146,NodeMinus17.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1136.p1147,GridMinus.atNode 1147,GridMinus.atNode 1148,NodeMinus17.w59,CompactMinus1136.checked1147,CompactMinus1136.small1147,CompactMinus1136.nodes1147,NodeMinus17.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1136.p1148,GridMinus.atNode 1148,GridMinus.atNode 1149,NodeMinus17.w60,CompactMinus1136.checked1148,CompactMinus1136.small1148,CompactMinus1136.nodes1148,NodeMinus17.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1136.p1149,GridMinus.atNode 1149,GridMinus.atNode 1150,NodeMinus17.w61,CompactMinus1136.checked1149,CompactMinus1136.small1149,CompactMinus1136.nodes1149,NodeMinus17.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1136.p1150,GridMinus.atNode 1150,GridMinus.atNode 1151,NodeMinus17.w62,CompactMinus1136.checked1150,CompactMinus1136.small1150,CompactMinus1136.nodes1150,NodeMinus17.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1136.p1151,GridMinus.atNode 1151,GridMinus.atNode 1152,NodeMinus17.w63,CompactMinus1136.checked1151,CompactMinus1136.small1151,CompactMinus1136.nodes1151,NodeMinus17.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (1088+j) ∧
    (atRow j).right=GridMinus.atNode (1088+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus17
