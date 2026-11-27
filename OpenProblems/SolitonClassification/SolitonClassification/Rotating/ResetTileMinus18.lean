import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus1152
import SolitonClassification.Rotating.ResetPackedMinus1168
import SolitonClassification.Rotating.ResetPackedMinus1184
import SolitonClassification.Rotating.ResetPackedMinus1200
namespace SolitonClassification.Rotating.DyadicReset.TileMinus18
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1152.p1152,GridMinus.atNode 1152,GridMinus.atNode 1153,NodeMinus18.w0,CompactMinus1152.checked1152,CompactMinus1152.small1152,CompactMinus1152.nodes1152,NodeMinus18.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1152.p1153,GridMinus.atNode 1153,GridMinus.atNode 1154,NodeMinus18.w1,CompactMinus1152.checked1153,CompactMinus1152.small1153,CompactMinus1152.nodes1153,NodeMinus18.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1152.p1154,GridMinus.atNode 1154,GridMinus.atNode 1155,NodeMinus18.w2,CompactMinus1152.checked1154,CompactMinus1152.small1154,CompactMinus1152.nodes1154,NodeMinus18.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1152.p1155,GridMinus.atNode 1155,GridMinus.atNode 1156,NodeMinus18.w3,CompactMinus1152.checked1155,CompactMinus1152.small1155,CompactMinus1152.nodes1155,NodeMinus18.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1152.p1156,GridMinus.atNode 1156,GridMinus.atNode 1157,NodeMinus18.w4,CompactMinus1152.checked1156,CompactMinus1152.small1156,CompactMinus1152.nodes1156,NodeMinus18.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1152.p1157,GridMinus.atNode 1157,GridMinus.atNode 1158,NodeMinus18.w5,CompactMinus1152.checked1157,CompactMinus1152.small1157,CompactMinus1152.nodes1157,NodeMinus18.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1152.p1158,GridMinus.atNode 1158,GridMinus.atNode 1159,NodeMinus18.w6,CompactMinus1152.checked1158,CompactMinus1152.small1158,CompactMinus1152.nodes1158,NodeMinus18.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1152.p1159,GridMinus.atNode 1159,GridMinus.atNode 1160,NodeMinus18.w7,CompactMinus1152.checked1159,CompactMinus1152.small1159,CompactMinus1152.nodes1159,NodeMinus18.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1152.p1160,GridMinus.atNode 1160,GridMinus.atNode 1161,NodeMinus18.w8,CompactMinus1152.checked1160,CompactMinus1152.small1160,CompactMinus1152.nodes1160,NodeMinus18.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1152.p1161,GridMinus.atNode 1161,GridMinus.atNode 1162,NodeMinus18.w9,CompactMinus1152.checked1161,CompactMinus1152.small1161,CompactMinus1152.nodes1161,NodeMinus18.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1152.p1162,GridMinus.atNode 1162,GridMinus.atNode 1163,NodeMinus18.w10,CompactMinus1152.checked1162,CompactMinus1152.small1162,CompactMinus1152.nodes1162,NodeMinus18.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1152.p1163,GridMinus.atNode 1163,GridMinus.atNode 1164,NodeMinus18.w11,CompactMinus1152.checked1163,CompactMinus1152.small1163,CompactMinus1152.nodes1163,NodeMinus18.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1152.p1164,GridMinus.atNode 1164,GridMinus.atNode 1165,NodeMinus18.w12,CompactMinus1152.checked1164,CompactMinus1152.small1164,CompactMinus1152.nodes1164,NodeMinus18.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1152.p1165,GridMinus.atNode 1165,GridMinus.atNode 1166,NodeMinus18.w13,CompactMinus1152.checked1165,CompactMinus1152.small1165,CompactMinus1152.nodes1165,NodeMinus18.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1152.p1166,GridMinus.atNode 1166,GridMinus.atNode 1167,NodeMinus18.w14,CompactMinus1152.checked1166,CompactMinus1152.small1166,CompactMinus1152.nodes1166,NodeMinus18.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1152.p1167,GridMinus.atNode 1167,GridMinus.atNode 1168,NodeMinus18.w15,CompactMinus1152.checked1167,CompactMinus1152.small1167,CompactMinus1152.nodes1167,NodeMinus18.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1168.p1168,GridMinus.atNode 1168,GridMinus.atNode 1169,NodeMinus18.w16,CompactMinus1168.checked1168,CompactMinus1168.small1168,CompactMinus1168.nodes1168,NodeMinus18.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1168.p1169,GridMinus.atNode 1169,GridMinus.atNode 1170,NodeMinus18.w17,CompactMinus1168.checked1169,CompactMinus1168.small1169,CompactMinus1168.nodes1169,NodeMinus18.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1168.p1170,GridMinus.atNode 1170,GridMinus.atNode 1171,NodeMinus18.w18,CompactMinus1168.checked1170,CompactMinus1168.small1170,CompactMinus1168.nodes1170,NodeMinus18.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1168.p1171,GridMinus.atNode 1171,GridMinus.atNode 1172,NodeMinus18.w19,CompactMinus1168.checked1171,CompactMinus1168.small1171,CompactMinus1168.nodes1171,NodeMinus18.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1168.p1172,GridMinus.atNode 1172,GridMinus.atNode 1173,NodeMinus18.w20,CompactMinus1168.checked1172,CompactMinus1168.small1172,CompactMinus1168.nodes1172,NodeMinus18.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1168.p1173,GridMinus.atNode 1173,GridMinus.atNode 1174,NodeMinus18.w21,CompactMinus1168.checked1173,CompactMinus1168.small1173,CompactMinus1168.nodes1173,NodeMinus18.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1168.p1174,GridMinus.atNode 1174,GridMinus.atNode 1175,NodeMinus18.w22,CompactMinus1168.checked1174,CompactMinus1168.small1174,CompactMinus1168.nodes1174,NodeMinus18.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1168.p1175,GridMinus.atNode 1175,GridMinus.atNode 1176,NodeMinus18.w23,CompactMinus1168.checked1175,CompactMinus1168.small1175,CompactMinus1168.nodes1175,NodeMinus18.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1168.p1176,GridMinus.atNode 1176,GridMinus.atNode 1177,NodeMinus18.w24,CompactMinus1168.checked1176,CompactMinus1168.small1176,CompactMinus1168.nodes1176,NodeMinus18.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1168.p1177,GridMinus.atNode 1177,GridMinus.atNode 1178,NodeMinus18.w25,CompactMinus1168.checked1177,CompactMinus1168.small1177,CompactMinus1168.nodes1177,NodeMinus18.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1168.p1178,GridMinus.atNode 1178,GridMinus.atNode 1179,NodeMinus18.w26,CompactMinus1168.checked1178,CompactMinus1168.small1178,CompactMinus1168.nodes1178,NodeMinus18.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1168.p1179,GridMinus.atNode 1179,GridMinus.atNode 1180,NodeMinus18.w27,CompactMinus1168.checked1179,CompactMinus1168.small1179,CompactMinus1168.nodes1179,NodeMinus18.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1168.p1180,GridMinus.atNode 1180,GridMinus.atNode 1181,NodeMinus18.w28,CompactMinus1168.checked1180,CompactMinus1168.small1180,CompactMinus1168.nodes1180,NodeMinus18.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1168.p1181,GridMinus.atNode 1181,GridMinus.atNode 1182,NodeMinus18.w29,CompactMinus1168.checked1181,CompactMinus1168.small1181,CompactMinus1168.nodes1181,NodeMinus18.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1168.p1182,GridMinus.atNode 1182,GridMinus.atNode 1183,NodeMinus18.w30,CompactMinus1168.checked1182,CompactMinus1168.small1182,CompactMinus1168.nodes1182,NodeMinus18.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1168.p1183,GridMinus.atNode 1183,GridMinus.atNode 1184,NodeMinus18.w31,CompactMinus1168.checked1183,CompactMinus1168.small1183,CompactMinus1168.nodes1183,NodeMinus18.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1184.p1184,GridMinus.atNode 1184,GridMinus.atNode 1185,NodeMinus18.w32,CompactMinus1184.checked1184,CompactMinus1184.small1184,CompactMinus1184.nodes1184,NodeMinus18.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1184.p1185,GridMinus.atNode 1185,GridMinus.atNode 1186,NodeMinus18.w33,CompactMinus1184.checked1185,CompactMinus1184.small1185,CompactMinus1184.nodes1185,NodeMinus18.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1184.p1186,GridMinus.atNode 1186,GridMinus.atNode 1187,NodeMinus18.w34,CompactMinus1184.checked1186,CompactMinus1184.small1186,CompactMinus1184.nodes1186,NodeMinus18.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1184.p1187,GridMinus.atNode 1187,GridMinus.atNode 1188,NodeMinus18.w35,CompactMinus1184.checked1187,CompactMinus1184.small1187,CompactMinus1184.nodes1187,NodeMinus18.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1184.p1188,GridMinus.atNode 1188,GridMinus.atNode 1189,NodeMinus18.w36,CompactMinus1184.checked1188,CompactMinus1184.small1188,CompactMinus1184.nodes1188,NodeMinus18.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1184.p1189,GridMinus.atNode 1189,GridMinus.atNode 1190,NodeMinus18.w37,CompactMinus1184.checked1189,CompactMinus1184.small1189,CompactMinus1184.nodes1189,NodeMinus18.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1184.p1190,GridMinus.atNode 1190,GridMinus.atNode 1191,NodeMinus18.w38,CompactMinus1184.checked1190,CompactMinus1184.small1190,CompactMinus1184.nodes1190,NodeMinus18.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1184.p1191,GridMinus.atNode 1191,GridMinus.atNode 1192,NodeMinus18.w39,CompactMinus1184.checked1191,CompactMinus1184.small1191,CompactMinus1184.nodes1191,NodeMinus18.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1184.p1192,GridMinus.atNode 1192,GridMinus.atNode 1193,NodeMinus18.w40,CompactMinus1184.checked1192,CompactMinus1184.small1192,CompactMinus1184.nodes1192,NodeMinus18.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1184.p1193,GridMinus.atNode 1193,GridMinus.atNode 1194,NodeMinus18.w41,CompactMinus1184.checked1193,CompactMinus1184.small1193,CompactMinus1184.nodes1193,NodeMinus18.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1184.p1194,GridMinus.atNode 1194,GridMinus.atNode 1195,NodeMinus18.w42,CompactMinus1184.checked1194,CompactMinus1184.small1194,CompactMinus1184.nodes1194,NodeMinus18.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1184.p1195,GridMinus.atNode 1195,GridMinus.atNode 1196,NodeMinus18.w43,CompactMinus1184.checked1195,CompactMinus1184.small1195,CompactMinus1184.nodes1195,NodeMinus18.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1184.p1196,GridMinus.atNode 1196,GridMinus.atNode 1197,NodeMinus18.w44,CompactMinus1184.checked1196,CompactMinus1184.small1196,CompactMinus1184.nodes1196,NodeMinus18.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1184.p1197,GridMinus.atNode 1197,GridMinus.atNode 1198,NodeMinus18.w45,CompactMinus1184.checked1197,CompactMinus1184.small1197,CompactMinus1184.nodes1197,NodeMinus18.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1184.p1198,GridMinus.atNode 1198,GridMinus.atNode 1199,NodeMinus18.w46,CompactMinus1184.checked1198,CompactMinus1184.small1198,CompactMinus1184.nodes1198,NodeMinus18.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1184.p1199,GridMinus.atNode 1199,GridMinus.atNode 1200,NodeMinus18.w47,CompactMinus1184.checked1199,CompactMinus1184.small1199,CompactMinus1184.nodes1199,NodeMinus18.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1200.p1200,GridMinus.atNode 1200,GridMinus.atNode 1201,NodeMinus18.w48,CompactMinus1200.checked1200,CompactMinus1200.small1200,CompactMinus1200.nodes1200,NodeMinus18.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1200.p1201,GridMinus.atNode 1201,GridMinus.atNode 1202,NodeMinus18.w49,CompactMinus1200.checked1201,CompactMinus1200.small1201,CompactMinus1200.nodes1201,NodeMinus18.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1200.p1202,GridMinus.atNode 1202,GridMinus.atNode 1203,NodeMinus18.w50,CompactMinus1200.checked1202,CompactMinus1200.small1202,CompactMinus1200.nodes1202,NodeMinus18.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1200.p1203,GridMinus.atNode 1203,GridMinus.atNode 1204,NodeMinus18.w51,CompactMinus1200.checked1203,CompactMinus1200.small1203,CompactMinus1200.nodes1203,NodeMinus18.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1200.p1204,GridMinus.atNode 1204,GridMinus.atNode 1205,NodeMinus18.w52,CompactMinus1200.checked1204,CompactMinus1200.small1204,CompactMinus1200.nodes1204,NodeMinus18.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1200.p1205,GridMinus.atNode 1205,GridMinus.atNode 1206,NodeMinus18.w53,CompactMinus1200.checked1205,CompactMinus1200.small1205,CompactMinus1200.nodes1205,NodeMinus18.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1200.p1206,GridMinus.atNode 1206,GridMinus.atNode 1207,NodeMinus18.w54,CompactMinus1200.checked1206,CompactMinus1200.small1206,CompactMinus1200.nodes1206,NodeMinus18.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1200.p1207,GridMinus.atNode 1207,GridMinus.atNode 1208,NodeMinus18.w55,CompactMinus1200.checked1207,CompactMinus1200.small1207,CompactMinus1200.nodes1207,NodeMinus18.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1200.p1208,GridMinus.atNode 1208,GridMinus.atNode 1209,NodeMinus18.w56,CompactMinus1200.checked1208,CompactMinus1200.small1208,CompactMinus1200.nodes1208,NodeMinus18.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1200.p1209,GridMinus.atNode 1209,GridMinus.atNode 1210,NodeMinus18.w57,CompactMinus1200.checked1209,CompactMinus1200.small1209,CompactMinus1200.nodes1209,NodeMinus18.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1200.p1210,GridMinus.atNode 1210,GridMinus.atNode 1211,NodeMinus18.w58,CompactMinus1200.checked1210,CompactMinus1200.small1210,CompactMinus1200.nodes1210,NodeMinus18.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1200.p1211,GridMinus.atNode 1211,GridMinus.atNode 1212,NodeMinus18.w59,CompactMinus1200.checked1211,CompactMinus1200.small1211,CompactMinus1200.nodes1211,NodeMinus18.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1200.p1212,GridMinus.atNode 1212,GridMinus.atNode 1213,NodeMinus18.w60,CompactMinus1200.checked1212,CompactMinus1200.small1212,CompactMinus1200.nodes1212,NodeMinus18.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1200.p1213,GridMinus.atNode 1213,GridMinus.atNode 1214,NodeMinus18.w61,CompactMinus1200.checked1213,CompactMinus1200.small1213,CompactMinus1200.nodes1213,NodeMinus18.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1200.p1214,GridMinus.atNode 1214,GridMinus.atNode 1215,NodeMinus18.w62,CompactMinus1200.checked1214,CompactMinus1200.small1214,CompactMinus1200.nodes1214,NodeMinus18.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1200.p1215,GridMinus.atNode 1215,GridMinus.atNode 1216,NodeMinus18.w63,CompactMinus1200.checked1215,CompactMinus1200.small1215,CompactMinus1200.nodes1215,NodeMinus18.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (1152+j) ∧
    (atRow j).right=GridMinus.atNode (1152+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus18
