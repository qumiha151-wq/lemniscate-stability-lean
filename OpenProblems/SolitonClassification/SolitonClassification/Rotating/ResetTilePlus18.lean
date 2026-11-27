import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus1152
import SolitonClassification.Rotating.ResetPackedPlus1168
import SolitonClassification.Rotating.ResetPackedPlus1184
import SolitonClassification.Rotating.ResetPackedPlus1200
namespace SolitonClassification.Rotating.DyadicReset.TilePlus18
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus1152.p1152,GridPlus.atNode 1152,GridPlus.atNode 1153,NodePlus18.w0,CompactPlus1152.checked1152,CompactPlus1152.small1152,CompactPlus1152.nodes1152,NodePlus18.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus1152.p1153,GridPlus.atNode 1153,GridPlus.atNode 1154,NodePlus18.w1,CompactPlus1152.checked1153,CompactPlus1152.small1153,CompactPlus1152.nodes1153,NodePlus18.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus1152.p1154,GridPlus.atNode 1154,GridPlus.atNode 1155,NodePlus18.w2,CompactPlus1152.checked1154,CompactPlus1152.small1154,CompactPlus1152.nodes1154,NodePlus18.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus1152.p1155,GridPlus.atNode 1155,GridPlus.atNode 1156,NodePlus18.w3,CompactPlus1152.checked1155,CompactPlus1152.small1155,CompactPlus1152.nodes1155,NodePlus18.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus1152.p1156,GridPlus.atNode 1156,GridPlus.atNode 1157,NodePlus18.w4,CompactPlus1152.checked1156,CompactPlus1152.small1156,CompactPlus1152.nodes1156,NodePlus18.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus1152.p1157,GridPlus.atNode 1157,GridPlus.atNode 1158,NodePlus18.w5,CompactPlus1152.checked1157,CompactPlus1152.small1157,CompactPlus1152.nodes1157,NodePlus18.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus1152.p1158,GridPlus.atNode 1158,GridPlus.atNode 1159,NodePlus18.w6,CompactPlus1152.checked1158,CompactPlus1152.small1158,CompactPlus1152.nodes1158,NodePlus18.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus1152.p1159,GridPlus.atNode 1159,GridPlus.atNode 1160,NodePlus18.w7,CompactPlus1152.checked1159,CompactPlus1152.small1159,CompactPlus1152.nodes1159,NodePlus18.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus1152.p1160,GridPlus.atNode 1160,GridPlus.atNode 1161,NodePlus18.w8,CompactPlus1152.checked1160,CompactPlus1152.small1160,CompactPlus1152.nodes1160,NodePlus18.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus1152.p1161,GridPlus.atNode 1161,GridPlus.atNode 1162,NodePlus18.w9,CompactPlus1152.checked1161,CompactPlus1152.small1161,CompactPlus1152.nodes1161,NodePlus18.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus1152.p1162,GridPlus.atNode 1162,GridPlus.atNode 1163,NodePlus18.w10,CompactPlus1152.checked1162,CompactPlus1152.small1162,CompactPlus1152.nodes1162,NodePlus18.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus1152.p1163,GridPlus.atNode 1163,GridPlus.atNode 1164,NodePlus18.w11,CompactPlus1152.checked1163,CompactPlus1152.small1163,CompactPlus1152.nodes1163,NodePlus18.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus1152.p1164,GridPlus.atNode 1164,GridPlus.atNode 1165,NodePlus18.w12,CompactPlus1152.checked1164,CompactPlus1152.small1164,CompactPlus1152.nodes1164,NodePlus18.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus1152.p1165,GridPlus.atNode 1165,GridPlus.atNode 1166,NodePlus18.w13,CompactPlus1152.checked1165,CompactPlus1152.small1165,CompactPlus1152.nodes1165,NodePlus18.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus1152.p1166,GridPlus.atNode 1166,GridPlus.atNode 1167,NodePlus18.w14,CompactPlus1152.checked1166,CompactPlus1152.small1166,CompactPlus1152.nodes1166,NodePlus18.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus1152.p1167,GridPlus.atNode 1167,GridPlus.atNode 1168,NodePlus18.w15,CompactPlus1152.checked1167,CompactPlus1152.small1167,CompactPlus1152.nodes1167,NodePlus18.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus1168.p1168,GridPlus.atNode 1168,GridPlus.atNode 1169,NodePlus18.w16,CompactPlus1168.checked1168,CompactPlus1168.small1168,CompactPlus1168.nodes1168,NodePlus18.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus1168.p1169,GridPlus.atNode 1169,GridPlus.atNode 1170,NodePlus18.w17,CompactPlus1168.checked1169,CompactPlus1168.small1169,CompactPlus1168.nodes1169,NodePlus18.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus1168.p1170,GridPlus.atNode 1170,GridPlus.atNode 1171,NodePlus18.w18,CompactPlus1168.checked1170,CompactPlus1168.small1170,CompactPlus1168.nodes1170,NodePlus18.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus1168.p1171,GridPlus.atNode 1171,GridPlus.atNode 1172,NodePlus18.w19,CompactPlus1168.checked1171,CompactPlus1168.small1171,CompactPlus1168.nodes1171,NodePlus18.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus1168.p1172,GridPlus.atNode 1172,GridPlus.atNode 1173,NodePlus18.w20,CompactPlus1168.checked1172,CompactPlus1168.small1172,CompactPlus1168.nodes1172,NodePlus18.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus1168.p1173,GridPlus.atNode 1173,GridPlus.atNode 1174,NodePlus18.w21,CompactPlus1168.checked1173,CompactPlus1168.small1173,CompactPlus1168.nodes1173,NodePlus18.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus1168.p1174,GridPlus.atNode 1174,GridPlus.atNode 1175,NodePlus18.w22,CompactPlus1168.checked1174,CompactPlus1168.small1174,CompactPlus1168.nodes1174,NodePlus18.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus1168.p1175,GridPlus.atNode 1175,GridPlus.atNode 1176,NodePlus18.w23,CompactPlus1168.checked1175,CompactPlus1168.small1175,CompactPlus1168.nodes1175,NodePlus18.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus1168.p1176,GridPlus.atNode 1176,GridPlus.atNode 1177,NodePlus18.w24,CompactPlus1168.checked1176,CompactPlus1168.small1176,CompactPlus1168.nodes1176,NodePlus18.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus1168.p1177,GridPlus.atNode 1177,GridPlus.atNode 1178,NodePlus18.w25,CompactPlus1168.checked1177,CompactPlus1168.small1177,CompactPlus1168.nodes1177,NodePlus18.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus1168.p1178,GridPlus.atNode 1178,GridPlus.atNode 1179,NodePlus18.w26,CompactPlus1168.checked1178,CompactPlus1168.small1178,CompactPlus1168.nodes1178,NodePlus18.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus1168.p1179,GridPlus.atNode 1179,GridPlus.atNode 1180,NodePlus18.w27,CompactPlus1168.checked1179,CompactPlus1168.small1179,CompactPlus1168.nodes1179,NodePlus18.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus1168.p1180,GridPlus.atNode 1180,GridPlus.atNode 1181,NodePlus18.w28,CompactPlus1168.checked1180,CompactPlus1168.small1180,CompactPlus1168.nodes1180,NodePlus18.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus1168.p1181,GridPlus.atNode 1181,GridPlus.atNode 1182,NodePlus18.w29,CompactPlus1168.checked1181,CompactPlus1168.small1181,CompactPlus1168.nodes1181,NodePlus18.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus1168.p1182,GridPlus.atNode 1182,GridPlus.atNode 1183,NodePlus18.w30,CompactPlus1168.checked1182,CompactPlus1168.small1182,CompactPlus1168.nodes1182,NodePlus18.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus1168.p1183,GridPlus.atNode 1183,GridPlus.atNode 1184,NodePlus18.w31,CompactPlus1168.checked1183,CompactPlus1168.small1183,CompactPlus1168.nodes1183,NodePlus18.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus1184.p1184,GridPlus.atNode 1184,GridPlus.atNode 1185,NodePlus18.w32,CompactPlus1184.checked1184,CompactPlus1184.small1184,CompactPlus1184.nodes1184,NodePlus18.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus1184.p1185,GridPlus.atNode 1185,GridPlus.atNode 1186,NodePlus18.w33,CompactPlus1184.checked1185,CompactPlus1184.small1185,CompactPlus1184.nodes1185,NodePlus18.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus1184.p1186,GridPlus.atNode 1186,GridPlus.atNode 1187,NodePlus18.w34,CompactPlus1184.checked1186,CompactPlus1184.small1186,CompactPlus1184.nodes1186,NodePlus18.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus1184.p1187,GridPlus.atNode 1187,GridPlus.atNode 1188,NodePlus18.w35,CompactPlus1184.checked1187,CompactPlus1184.small1187,CompactPlus1184.nodes1187,NodePlus18.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus1184.p1188,GridPlus.atNode 1188,GridPlus.atNode 1189,NodePlus18.w36,CompactPlus1184.checked1188,CompactPlus1184.small1188,CompactPlus1184.nodes1188,NodePlus18.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus1184.p1189,GridPlus.atNode 1189,GridPlus.atNode 1190,NodePlus18.w37,CompactPlus1184.checked1189,CompactPlus1184.small1189,CompactPlus1184.nodes1189,NodePlus18.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus1184.p1190,GridPlus.atNode 1190,GridPlus.atNode 1191,NodePlus18.w38,CompactPlus1184.checked1190,CompactPlus1184.small1190,CompactPlus1184.nodes1190,NodePlus18.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus1184.p1191,GridPlus.atNode 1191,GridPlus.atNode 1192,NodePlus18.w39,CompactPlus1184.checked1191,CompactPlus1184.small1191,CompactPlus1184.nodes1191,NodePlus18.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus1184.p1192,GridPlus.atNode 1192,GridPlus.atNode 1193,NodePlus18.w40,CompactPlus1184.checked1192,CompactPlus1184.small1192,CompactPlus1184.nodes1192,NodePlus18.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus1184.p1193,GridPlus.atNode 1193,GridPlus.atNode 1194,NodePlus18.w41,CompactPlus1184.checked1193,CompactPlus1184.small1193,CompactPlus1184.nodes1193,NodePlus18.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus1184.p1194,GridPlus.atNode 1194,GridPlus.atNode 1195,NodePlus18.w42,CompactPlus1184.checked1194,CompactPlus1184.small1194,CompactPlus1184.nodes1194,NodePlus18.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus1184.p1195,GridPlus.atNode 1195,GridPlus.atNode 1196,NodePlus18.w43,CompactPlus1184.checked1195,CompactPlus1184.small1195,CompactPlus1184.nodes1195,NodePlus18.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus1184.p1196,GridPlus.atNode 1196,GridPlus.atNode 1197,NodePlus18.w44,CompactPlus1184.checked1196,CompactPlus1184.small1196,CompactPlus1184.nodes1196,NodePlus18.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus1184.p1197,GridPlus.atNode 1197,GridPlus.atNode 1198,NodePlus18.w45,CompactPlus1184.checked1197,CompactPlus1184.small1197,CompactPlus1184.nodes1197,NodePlus18.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus1184.p1198,GridPlus.atNode 1198,GridPlus.atNode 1199,NodePlus18.w46,CompactPlus1184.checked1198,CompactPlus1184.small1198,CompactPlus1184.nodes1198,NodePlus18.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus1184.p1199,GridPlus.atNode 1199,GridPlus.atNode 1200,NodePlus18.w47,CompactPlus1184.checked1199,CompactPlus1184.small1199,CompactPlus1184.nodes1199,NodePlus18.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus1200.p1200,GridPlus.atNode 1200,GridPlus.atNode 1201,NodePlus18.w48,CompactPlus1200.checked1200,CompactPlus1200.small1200,CompactPlus1200.nodes1200,NodePlus18.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus1200.p1201,GridPlus.atNode 1201,GridPlus.atNode 1202,NodePlus18.w49,CompactPlus1200.checked1201,CompactPlus1200.small1201,CompactPlus1200.nodes1201,NodePlus18.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus1200.p1202,GridPlus.atNode 1202,GridPlus.atNode 1203,NodePlus18.w50,CompactPlus1200.checked1202,CompactPlus1200.small1202,CompactPlus1200.nodes1202,NodePlus18.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus1200.p1203,GridPlus.atNode 1203,GridPlus.atNode 1204,NodePlus18.w51,CompactPlus1200.checked1203,CompactPlus1200.small1203,CompactPlus1200.nodes1203,NodePlus18.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus1200.p1204,GridPlus.atNode 1204,GridPlus.atNode 1205,NodePlus18.w52,CompactPlus1200.checked1204,CompactPlus1200.small1204,CompactPlus1200.nodes1204,NodePlus18.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus1200.p1205,GridPlus.atNode 1205,GridPlus.atNode 1206,NodePlus18.w53,CompactPlus1200.checked1205,CompactPlus1200.small1205,CompactPlus1200.nodes1205,NodePlus18.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus1200.p1206,GridPlus.atNode 1206,GridPlus.atNode 1207,NodePlus18.w54,CompactPlus1200.checked1206,CompactPlus1200.small1206,CompactPlus1200.nodes1206,NodePlus18.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus1200.p1207,GridPlus.atNode 1207,GridPlus.atNode 1208,NodePlus18.w55,CompactPlus1200.checked1207,CompactPlus1200.small1207,CompactPlus1200.nodes1207,NodePlus18.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus1200.p1208,GridPlus.atNode 1208,GridPlus.atNode 1209,NodePlus18.w56,CompactPlus1200.checked1208,CompactPlus1200.small1208,CompactPlus1200.nodes1208,NodePlus18.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus1200.p1209,GridPlus.atNode 1209,GridPlus.atNode 1210,NodePlus18.w57,CompactPlus1200.checked1209,CompactPlus1200.small1209,CompactPlus1200.nodes1209,NodePlus18.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus1200.p1210,GridPlus.atNode 1210,GridPlus.atNode 1211,NodePlus18.w58,CompactPlus1200.checked1210,CompactPlus1200.small1210,CompactPlus1200.nodes1210,NodePlus18.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus1200.p1211,GridPlus.atNode 1211,GridPlus.atNode 1212,NodePlus18.w59,CompactPlus1200.checked1211,CompactPlus1200.small1211,CompactPlus1200.nodes1211,NodePlus18.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus1200.p1212,GridPlus.atNode 1212,GridPlus.atNode 1213,NodePlus18.w60,CompactPlus1200.checked1212,CompactPlus1200.small1212,CompactPlus1200.nodes1212,NodePlus18.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus1200.p1213,GridPlus.atNode 1213,GridPlus.atNode 1214,NodePlus18.w61,CompactPlus1200.checked1213,CompactPlus1200.small1213,CompactPlus1200.nodes1213,NodePlus18.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus1200.p1214,GridPlus.atNode 1214,GridPlus.atNode 1215,NodePlus18.w62,CompactPlus1200.checked1214,CompactPlus1200.small1214,CompactPlus1200.nodes1214,NodePlus18.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus1200.p1215,GridPlus.atNode 1215,GridPlus.atNode 1216,NodePlus18.w63,CompactPlus1200.checked1215,CompactPlus1200.small1215,CompactPlus1200.nodes1215,NodePlus18.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (1152+j) ∧
    (atRow j).right=GridPlus.atNode (1152+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus18
