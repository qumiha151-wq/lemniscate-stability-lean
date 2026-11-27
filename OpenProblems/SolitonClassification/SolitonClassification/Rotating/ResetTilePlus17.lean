import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus1088
import SolitonClassification.Rotating.ResetPackedPlus1104
import SolitonClassification.Rotating.ResetPackedPlus1120
import SolitonClassification.Rotating.ResetPackedPlus1136
namespace SolitonClassification.Rotating.DyadicReset.TilePlus17
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus1088.p1088,GridPlus.atNode 1088,GridPlus.atNode 1089,NodePlus17.w0,CompactPlus1088.checked1088,CompactPlus1088.small1088,CompactPlus1088.nodes1088,NodePlus17.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus1088.p1089,GridPlus.atNode 1089,GridPlus.atNode 1090,NodePlus17.w1,CompactPlus1088.checked1089,CompactPlus1088.small1089,CompactPlus1088.nodes1089,NodePlus17.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus1088.p1090,GridPlus.atNode 1090,GridPlus.atNode 1091,NodePlus17.w2,CompactPlus1088.checked1090,CompactPlus1088.small1090,CompactPlus1088.nodes1090,NodePlus17.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus1088.p1091,GridPlus.atNode 1091,GridPlus.atNode 1092,NodePlus17.w3,CompactPlus1088.checked1091,CompactPlus1088.small1091,CompactPlus1088.nodes1091,NodePlus17.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus1088.p1092,GridPlus.atNode 1092,GridPlus.atNode 1093,NodePlus17.w4,CompactPlus1088.checked1092,CompactPlus1088.small1092,CompactPlus1088.nodes1092,NodePlus17.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus1088.p1093,GridPlus.atNode 1093,GridPlus.atNode 1094,NodePlus17.w5,CompactPlus1088.checked1093,CompactPlus1088.small1093,CompactPlus1088.nodes1093,NodePlus17.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus1088.p1094,GridPlus.atNode 1094,GridPlus.atNode 1095,NodePlus17.w6,CompactPlus1088.checked1094,CompactPlus1088.small1094,CompactPlus1088.nodes1094,NodePlus17.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus1088.p1095,GridPlus.atNode 1095,GridPlus.atNode 1096,NodePlus17.w7,CompactPlus1088.checked1095,CompactPlus1088.small1095,CompactPlus1088.nodes1095,NodePlus17.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus1088.p1096,GridPlus.atNode 1096,GridPlus.atNode 1097,NodePlus17.w8,CompactPlus1088.checked1096,CompactPlus1088.small1096,CompactPlus1088.nodes1096,NodePlus17.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus1088.p1097,GridPlus.atNode 1097,GridPlus.atNode 1098,NodePlus17.w9,CompactPlus1088.checked1097,CompactPlus1088.small1097,CompactPlus1088.nodes1097,NodePlus17.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus1088.p1098,GridPlus.atNode 1098,GridPlus.atNode 1099,NodePlus17.w10,CompactPlus1088.checked1098,CompactPlus1088.small1098,CompactPlus1088.nodes1098,NodePlus17.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus1088.p1099,GridPlus.atNode 1099,GridPlus.atNode 1100,NodePlus17.w11,CompactPlus1088.checked1099,CompactPlus1088.small1099,CompactPlus1088.nodes1099,NodePlus17.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus1088.p1100,GridPlus.atNode 1100,GridPlus.atNode 1101,NodePlus17.w12,CompactPlus1088.checked1100,CompactPlus1088.small1100,CompactPlus1088.nodes1100,NodePlus17.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus1088.p1101,GridPlus.atNode 1101,GridPlus.atNode 1102,NodePlus17.w13,CompactPlus1088.checked1101,CompactPlus1088.small1101,CompactPlus1088.nodes1101,NodePlus17.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus1088.p1102,GridPlus.atNode 1102,GridPlus.atNode 1103,NodePlus17.w14,CompactPlus1088.checked1102,CompactPlus1088.small1102,CompactPlus1088.nodes1102,NodePlus17.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus1088.p1103,GridPlus.atNode 1103,GridPlus.atNode 1104,NodePlus17.w15,CompactPlus1088.checked1103,CompactPlus1088.small1103,CompactPlus1088.nodes1103,NodePlus17.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus1104.p1104,GridPlus.atNode 1104,GridPlus.atNode 1105,NodePlus17.w16,CompactPlus1104.checked1104,CompactPlus1104.small1104,CompactPlus1104.nodes1104,NodePlus17.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus1104.p1105,GridPlus.atNode 1105,GridPlus.atNode 1106,NodePlus17.w17,CompactPlus1104.checked1105,CompactPlus1104.small1105,CompactPlus1104.nodes1105,NodePlus17.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus1104.p1106,GridPlus.atNode 1106,GridPlus.atNode 1107,NodePlus17.w18,CompactPlus1104.checked1106,CompactPlus1104.small1106,CompactPlus1104.nodes1106,NodePlus17.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus1104.p1107,GridPlus.atNode 1107,GridPlus.atNode 1108,NodePlus17.w19,CompactPlus1104.checked1107,CompactPlus1104.small1107,CompactPlus1104.nodes1107,NodePlus17.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus1104.p1108,GridPlus.atNode 1108,GridPlus.atNode 1109,NodePlus17.w20,CompactPlus1104.checked1108,CompactPlus1104.small1108,CompactPlus1104.nodes1108,NodePlus17.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus1104.p1109,GridPlus.atNode 1109,GridPlus.atNode 1110,NodePlus17.w21,CompactPlus1104.checked1109,CompactPlus1104.small1109,CompactPlus1104.nodes1109,NodePlus17.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus1104.p1110,GridPlus.atNode 1110,GridPlus.atNode 1111,NodePlus17.w22,CompactPlus1104.checked1110,CompactPlus1104.small1110,CompactPlus1104.nodes1110,NodePlus17.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus1104.p1111,GridPlus.atNode 1111,GridPlus.atNode 1112,NodePlus17.w23,CompactPlus1104.checked1111,CompactPlus1104.small1111,CompactPlus1104.nodes1111,NodePlus17.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus1104.p1112,GridPlus.atNode 1112,GridPlus.atNode 1113,NodePlus17.w24,CompactPlus1104.checked1112,CompactPlus1104.small1112,CompactPlus1104.nodes1112,NodePlus17.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus1104.p1113,GridPlus.atNode 1113,GridPlus.atNode 1114,NodePlus17.w25,CompactPlus1104.checked1113,CompactPlus1104.small1113,CompactPlus1104.nodes1113,NodePlus17.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus1104.p1114,GridPlus.atNode 1114,GridPlus.atNode 1115,NodePlus17.w26,CompactPlus1104.checked1114,CompactPlus1104.small1114,CompactPlus1104.nodes1114,NodePlus17.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus1104.p1115,GridPlus.atNode 1115,GridPlus.atNode 1116,NodePlus17.w27,CompactPlus1104.checked1115,CompactPlus1104.small1115,CompactPlus1104.nodes1115,NodePlus17.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus1104.p1116,GridPlus.atNode 1116,GridPlus.atNode 1117,NodePlus17.w28,CompactPlus1104.checked1116,CompactPlus1104.small1116,CompactPlus1104.nodes1116,NodePlus17.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus1104.p1117,GridPlus.atNode 1117,GridPlus.atNode 1118,NodePlus17.w29,CompactPlus1104.checked1117,CompactPlus1104.small1117,CompactPlus1104.nodes1117,NodePlus17.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus1104.p1118,GridPlus.atNode 1118,GridPlus.atNode 1119,NodePlus17.w30,CompactPlus1104.checked1118,CompactPlus1104.small1118,CompactPlus1104.nodes1118,NodePlus17.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus1104.p1119,GridPlus.atNode 1119,GridPlus.atNode 1120,NodePlus17.w31,CompactPlus1104.checked1119,CompactPlus1104.small1119,CompactPlus1104.nodes1119,NodePlus17.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus1120.p1120,GridPlus.atNode 1120,GridPlus.atNode 1121,NodePlus17.w32,CompactPlus1120.checked1120,CompactPlus1120.small1120,CompactPlus1120.nodes1120,NodePlus17.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus1120.p1121,GridPlus.atNode 1121,GridPlus.atNode 1122,NodePlus17.w33,CompactPlus1120.checked1121,CompactPlus1120.small1121,CompactPlus1120.nodes1121,NodePlus17.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus1120.p1122,GridPlus.atNode 1122,GridPlus.atNode 1123,NodePlus17.w34,CompactPlus1120.checked1122,CompactPlus1120.small1122,CompactPlus1120.nodes1122,NodePlus17.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus1120.p1123,GridPlus.atNode 1123,GridPlus.atNode 1124,NodePlus17.w35,CompactPlus1120.checked1123,CompactPlus1120.small1123,CompactPlus1120.nodes1123,NodePlus17.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus1120.p1124,GridPlus.atNode 1124,GridPlus.atNode 1125,NodePlus17.w36,CompactPlus1120.checked1124,CompactPlus1120.small1124,CompactPlus1120.nodes1124,NodePlus17.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus1120.p1125,GridPlus.atNode 1125,GridPlus.atNode 1126,NodePlus17.w37,CompactPlus1120.checked1125,CompactPlus1120.small1125,CompactPlus1120.nodes1125,NodePlus17.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus1120.p1126,GridPlus.atNode 1126,GridPlus.atNode 1127,NodePlus17.w38,CompactPlus1120.checked1126,CompactPlus1120.small1126,CompactPlus1120.nodes1126,NodePlus17.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus1120.p1127,GridPlus.atNode 1127,GridPlus.atNode 1128,NodePlus17.w39,CompactPlus1120.checked1127,CompactPlus1120.small1127,CompactPlus1120.nodes1127,NodePlus17.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus1120.p1128,GridPlus.atNode 1128,GridPlus.atNode 1129,NodePlus17.w40,CompactPlus1120.checked1128,CompactPlus1120.small1128,CompactPlus1120.nodes1128,NodePlus17.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus1120.p1129,GridPlus.atNode 1129,GridPlus.atNode 1130,NodePlus17.w41,CompactPlus1120.checked1129,CompactPlus1120.small1129,CompactPlus1120.nodes1129,NodePlus17.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus1120.p1130,GridPlus.atNode 1130,GridPlus.atNode 1131,NodePlus17.w42,CompactPlus1120.checked1130,CompactPlus1120.small1130,CompactPlus1120.nodes1130,NodePlus17.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus1120.p1131,GridPlus.atNode 1131,GridPlus.atNode 1132,NodePlus17.w43,CompactPlus1120.checked1131,CompactPlus1120.small1131,CompactPlus1120.nodes1131,NodePlus17.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus1120.p1132,GridPlus.atNode 1132,GridPlus.atNode 1133,NodePlus17.w44,CompactPlus1120.checked1132,CompactPlus1120.small1132,CompactPlus1120.nodes1132,NodePlus17.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus1120.p1133,GridPlus.atNode 1133,GridPlus.atNode 1134,NodePlus17.w45,CompactPlus1120.checked1133,CompactPlus1120.small1133,CompactPlus1120.nodes1133,NodePlus17.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus1120.p1134,GridPlus.atNode 1134,GridPlus.atNode 1135,NodePlus17.w46,CompactPlus1120.checked1134,CompactPlus1120.small1134,CompactPlus1120.nodes1134,NodePlus17.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus1120.p1135,GridPlus.atNode 1135,GridPlus.atNode 1136,NodePlus17.w47,CompactPlus1120.checked1135,CompactPlus1120.small1135,CompactPlus1120.nodes1135,NodePlus17.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus1136.p1136,GridPlus.atNode 1136,GridPlus.atNode 1137,NodePlus17.w48,CompactPlus1136.checked1136,CompactPlus1136.small1136,CompactPlus1136.nodes1136,NodePlus17.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus1136.p1137,GridPlus.atNode 1137,GridPlus.atNode 1138,NodePlus17.w49,CompactPlus1136.checked1137,CompactPlus1136.small1137,CompactPlus1136.nodes1137,NodePlus17.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus1136.p1138,GridPlus.atNode 1138,GridPlus.atNode 1139,NodePlus17.w50,CompactPlus1136.checked1138,CompactPlus1136.small1138,CompactPlus1136.nodes1138,NodePlus17.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus1136.p1139,GridPlus.atNode 1139,GridPlus.atNode 1140,NodePlus17.w51,CompactPlus1136.checked1139,CompactPlus1136.small1139,CompactPlus1136.nodes1139,NodePlus17.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus1136.p1140,GridPlus.atNode 1140,GridPlus.atNode 1141,NodePlus17.w52,CompactPlus1136.checked1140,CompactPlus1136.small1140,CompactPlus1136.nodes1140,NodePlus17.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus1136.p1141,GridPlus.atNode 1141,GridPlus.atNode 1142,NodePlus17.w53,CompactPlus1136.checked1141,CompactPlus1136.small1141,CompactPlus1136.nodes1141,NodePlus17.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus1136.p1142,GridPlus.atNode 1142,GridPlus.atNode 1143,NodePlus17.w54,CompactPlus1136.checked1142,CompactPlus1136.small1142,CompactPlus1136.nodes1142,NodePlus17.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus1136.p1143,GridPlus.atNode 1143,GridPlus.atNode 1144,NodePlus17.w55,CompactPlus1136.checked1143,CompactPlus1136.small1143,CompactPlus1136.nodes1143,NodePlus17.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus1136.p1144,GridPlus.atNode 1144,GridPlus.atNode 1145,NodePlus17.w56,CompactPlus1136.checked1144,CompactPlus1136.small1144,CompactPlus1136.nodes1144,NodePlus17.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus1136.p1145,GridPlus.atNode 1145,GridPlus.atNode 1146,NodePlus17.w57,CompactPlus1136.checked1145,CompactPlus1136.small1145,CompactPlus1136.nodes1145,NodePlus17.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus1136.p1146,GridPlus.atNode 1146,GridPlus.atNode 1147,NodePlus17.w58,CompactPlus1136.checked1146,CompactPlus1136.small1146,CompactPlus1136.nodes1146,NodePlus17.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus1136.p1147,GridPlus.atNode 1147,GridPlus.atNode 1148,NodePlus17.w59,CompactPlus1136.checked1147,CompactPlus1136.small1147,CompactPlus1136.nodes1147,NodePlus17.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus1136.p1148,GridPlus.atNode 1148,GridPlus.atNode 1149,NodePlus17.w60,CompactPlus1136.checked1148,CompactPlus1136.small1148,CompactPlus1136.nodes1148,NodePlus17.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus1136.p1149,GridPlus.atNode 1149,GridPlus.atNode 1150,NodePlus17.w61,CompactPlus1136.checked1149,CompactPlus1136.small1149,CompactPlus1136.nodes1149,NodePlus17.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus1136.p1150,GridPlus.atNode 1150,GridPlus.atNode 1151,NodePlus17.w62,CompactPlus1136.checked1150,CompactPlus1136.small1150,CompactPlus1136.nodes1150,NodePlus17.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus1136.p1151,GridPlus.atNode 1151,GridPlus.atNode 1152,NodePlus17.w63,CompactPlus1136.checked1151,CompactPlus1136.small1151,CompactPlus1136.nodes1151,NodePlus17.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (1088+j) ∧
    (atRow j).right=GridPlus.atNode (1088+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus17
