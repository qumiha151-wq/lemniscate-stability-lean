import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus1216
import SolitonClassification.Rotating.ResetPackedMinus1232
import SolitonClassification.Rotating.ResetPackedMinus1248
import SolitonClassification.Rotating.ResetPackedMinus1264
namespace SolitonClassification.Rotating.DyadicReset.TileMinus19
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1216.p1216,GridMinus.atNode 1216,GridMinus.atNode 1217,NodeMinus19.w0,CompactMinus1216.checked1216,CompactMinus1216.small1216,CompactMinus1216.nodes1216,NodeMinus19.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1216.p1217,GridMinus.atNode 1217,GridMinus.atNode 1218,NodeMinus19.w1,CompactMinus1216.checked1217,CompactMinus1216.small1217,CompactMinus1216.nodes1217,NodeMinus19.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1216.p1218,GridMinus.atNode 1218,GridMinus.atNode 1219,NodeMinus19.w2,CompactMinus1216.checked1218,CompactMinus1216.small1218,CompactMinus1216.nodes1218,NodeMinus19.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1216.p1219,GridMinus.atNode 1219,GridMinus.atNode 1220,NodeMinus19.w3,CompactMinus1216.checked1219,CompactMinus1216.small1219,CompactMinus1216.nodes1219,NodeMinus19.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1216.p1220,GridMinus.atNode 1220,GridMinus.atNode 1221,NodeMinus19.w4,CompactMinus1216.checked1220,CompactMinus1216.small1220,CompactMinus1216.nodes1220,NodeMinus19.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1216.p1221,GridMinus.atNode 1221,GridMinus.atNode 1222,NodeMinus19.w5,CompactMinus1216.checked1221,CompactMinus1216.small1221,CompactMinus1216.nodes1221,NodeMinus19.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1216.p1222,GridMinus.atNode 1222,GridMinus.atNode 1223,NodeMinus19.w6,CompactMinus1216.checked1222,CompactMinus1216.small1222,CompactMinus1216.nodes1222,NodeMinus19.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1216.p1223,GridMinus.atNode 1223,GridMinus.atNode 1224,NodeMinus19.w7,CompactMinus1216.checked1223,CompactMinus1216.small1223,CompactMinus1216.nodes1223,NodeMinus19.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1216.p1224,GridMinus.atNode 1224,GridMinus.atNode 1225,NodeMinus19.w8,CompactMinus1216.checked1224,CompactMinus1216.small1224,CompactMinus1216.nodes1224,NodeMinus19.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1216.p1225,GridMinus.atNode 1225,GridMinus.atNode 1226,NodeMinus19.w9,CompactMinus1216.checked1225,CompactMinus1216.small1225,CompactMinus1216.nodes1225,NodeMinus19.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1216.p1226,GridMinus.atNode 1226,GridMinus.atNode 1227,NodeMinus19.w10,CompactMinus1216.checked1226,CompactMinus1216.small1226,CompactMinus1216.nodes1226,NodeMinus19.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1216.p1227,GridMinus.atNode 1227,GridMinus.atNode 1228,NodeMinus19.w11,CompactMinus1216.checked1227,CompactMinus1216.small1227,CompactMinus1216.nodes1227,NodeMinus19.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1216.p1228,GridMinus.atNode 1228,GridMinus.atNode 1229,NodeMinus19.w12,CompactMinus1216.checked1228,CompactMinus1216.small1228,CompactMinus1216.nodes1228,NodeMinus19.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1216.p1229,GridMinus.atNode 1229,GridMinus.atNode 1230,NodeMinus19.w13,CompactMinus1216.checked1229,CompactMinus1216.small1229,CompactMinus1216.nodes1229,NodeMinus19.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1216.p1230,GridMinus.atNode 1230,GridMinus.atNode 1231,NodeMinus19.w14,CompactMinus1216.checked1230,CompactMinus1216.small1230,CompactMinus1216.nodes1230,NodeMinus19.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1216.p1231,GridMinus.atNode 1231,GridMinus.atNode 1232,NodeMinus19.w15,CompactMinus1216.checked1231,CompactMinus1216.small1231,CompactMinus1216.nodes1231,NodeMinus19.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1232.p1232,GridMinus.atNode 1232,GridMinus.atNode 1233,NodeMinus19.w16,CompactMinus1232.checked1232,CompactMinus1232.small1232,CompactMinus1232.nodes1232,NodeMinus19.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1232.p1233,GridMinus.atNode 1233,GridMinus.atNode 1234,NodeMinus19.w17,CompactMinus1232.checked1233,CompactMinus1232.small1233,CompactMinus1232.nodes1233,NodeMinus19.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1232.p1234,GridMinus.atNode 1234,GridMinus.atNode 1235,NodeMinus19.w18,CompactMinus1232.checked1234,CompactMinus1232.small1234,CompactMinus1232.nodes1234,NodeMinus19.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1232.p1235,GridMinus.atNode 1235,GridMinus.atNode 1236,NodeMinus19.w19,CompactMinus1232.checked1235,CompactMinus1232.small1235,CompactMinus1232.nodes1235,NodeMinus19.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1232.p1236,GridMinus.atNode 1236,GridMinus.atNode 1237,NodeMinus19.w20,CompactMinus1232.checked1236,CompactMinus1232.small1236,CompactMinus1232.nodes1236,NodeMinus19.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1232.p1237,GridMinus.atNode 1237,GridMinus.atNode 1238,NodeMinus19.w21,CompactMinus1232.checked1237,CompactMinus1232.small1237,CompactMinus1232.nodes1237,NodeMinus19.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1232.p1238,GridMinus.atNode 1238,GridMinus.atNode 1239,NodeMinus19.w22,CompactMinus1232.checked1238,CompactMinus1232.small1238,CompactMinus1232.nodes1238,NodeMinus19.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1232.p1239,GridMinus.atNode 1239,GridMinus.atNode 1240,NodeMinus19.w23,CompactMinus1232.checked1239,CompactMinus1232.small1239,CompactMinus1232.nodes1239,NodeMinus19.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1232.p1240,GridMinus.atNode 1240,GridMinus.atNode 1241,NodeMinus19.w24,CompactMinus1232.checked1240,CompactMinus1232.small1240,CompactMinus1232.nodes1240,NodeMinus19.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1232.p1241,GridMinus.atNode 1241,GridMinus.atNode 1242,NodeMinus19.w25,CompactMinus1232.checked1241,CompactMinus1232.small1241,CompactMinus1232.nodes1241,NodeMinus19.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1232.p1242,GridMinus.atNode 1242,GridMinus.atNode 1243,NodeMinus19.w26,CompactMinus1232.checked1242,CompactMinus1232.small1242,CompactMinus1232.nodes1242,NodeMinus19.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1232.p1243,GridMinus.atNode 1243,GridMinus.atNode 1244,NodeMinus19.w27,CompactMinus1232.checked1243,CompactMinus1232.small1243,CompactMinus1232.nodes1243,NodeMinus19.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1232.p1244,GridMinus.atNode 1244,GridMinus.atNode 1245,NodeMinus19.w28,CompactMinus1232.checked1244,CompactMinus1232.small1244,CompactMinus1232.nodes1244,NodeMinus19.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1232.p1245,GridMinus.atNode 1245,GridMinus.atNode 1246,NodeMinus19.w29,CompactMinus1232.checked1245,CompactMinus1232.small1245,CompactMinus1232.nodes1245,NodeMinus19.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1232.p1246,GridMinus.atNode 1246,GridMinus.atNode 1247,NodeMinus19.w30,CompactMinus1232.checked1246,CompactMinus1232.small1246,CompactMinus1232.nodes1246,NodeMinus19.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1232.p1247,GridMinus.atNode 1247,GridMinus.atNode 1248,NodeMinus19.w31,CompactMinus1232.checked1247,CompactMinus1232.small1247,CompactMinus1232.nodes1247,NodeMinus19.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1248.p1248,GridMinus.atNode 1248,GridMinus.atNode 1249,NodeMinus19.w32,CompactMinus1248.checked1248,CompactMinus1248.small1248,CompactMinus1248.nodes1248,NodeMinus19.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1248.p1249,GridMinus.atNode 1249,GridMinus.atNode 1250,NodeMinus19.w33,CompactMinus1248.checked1249,CompactMinus1248.small1249,CompactMinus1248.nodes1249,NodeMinus19.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1248.p1250,GridMinus.atNode 1250,GridMinus.atNode 1251,NodeMinus19.w34,CompactMinus1248.checked1250,CompactMinus1248.small1250,CompactMinus1248.nodes1250,NodeMinus19.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1248.p1251,GridMinus.atNode 1251,GridMinus.atNode 1252,NodeMinus19.w35,CompactMinus1248.checked1251,CompactMinus1248.small1251,CompactMinus1248.nodes1251,NodeMinus19.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1248.p1252,GridMinus.atNode 1252,GridMinus.atNode 1253,NodeMinus19.w36,CompactMinus1248.checked1252,CompactMinus1248.small1252,CompactMinus1248.nodes1252,NodeMinus19.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1248.p1253,GridMinus.atNode 1253,GridMinus.atNode 1254,NodeMinus19.w37,CompactMinus1248.checked1253,CompactMinus1248.small1253,CompactMinus1248.nodes1253,NodeMinus19.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1248.p1254,GridMinus.atNode 1254,GridMinus.atNode 1255,NodeMinus19.w38,CompactMinus1248.checked1254,CompactMinus1248.small1254,CompactMinus1248.nodes1254,NodeMinus19.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1248.p1255,GridMinus.atNode 1255,GridMinus.atNode 1256,NodeMinus19.w39,CompactMinus1248.checked1255,CompactMinus1248.small1255,CompactMinus1248.nodes1255,NodeMinus19.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1248.p1256,GridMinus.atNode 1256,GridMinus.atNode 1257,NodeMinus19.w40,CompactMinus1248.checked1256,CompactMinus1248.small1256,CompactMinus1248.nodes1256,NodeMinus19.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1248.p1257,GridMinus.atNode 1257,GridMinus.atNode 1258,NodeMinus19.w41,CompactMinus1248.checked1257,CompactMinus1248.small1257,CompactMinus1248.nodes1257,NodeMinus19.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1248.p1258,GridMinus.atNode 1258,GridMinus.atNode 1259,NodeMinus19.w42,CompactMinus1248.checked1258,CompactMinus1248.small1258,CompactMinus1248.nodes1258,NodeMinus19.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1248.p1259,GridMinus.atNode 1259,GridMinus.atNode 1260,NodeMinus19.w43,CompactMinus1248.checked1259,CompactMinus1248.small1259,CompactMinus1248.nodes1259,NodeMinus19.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1248.p1260,GridMinus.atNode 1260,GridMinus.atNode 1261,NodeMinus19.w44,CompactMinus1248.checked1260,CompactMinus1248.small1260,CompactMinus1248.nodes1260,NodeMinus19.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1248.p1261,GridMinus.atNode 1261,GridMinus.atNode 1262,NodeMinus19.w45,CompactMinus1248.checked1261,CompactMinus1248.small1261,CompactMinus1248.nodes1261,NodeMinus19.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1248.p1262,GridMinus.atNode 1262,GridMinus.atNode 1263,NodeMinus19.w46,CompactMinus1248.checked1262,CompactMinus1248.small1262,CompactMinus1248.nodes1262,NodeMinus19.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1248.p1263,GridMinus.atNode 1263,GridMinus.atNode 1264,NodeMinus19.w47,CompactMinus1248.checked1263,CompactMinus1248.small1263,CompactMinus1248.nodes1263,NodeMinus19.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1264.p1264,GridMinus.atNode 1264,GridMinus.atNode 1265,NodeMinus19.w48,CompactMinus1264.checked1264,CompactMinus1264.small1264,CompactMinus1264.nodes1264,NodeMinus19.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1264.p1265,GridMinus.atNode 1265,GridMinus.atNode 1266,NodeMinus19.w49,CompactMinus1264.checked1265,CompactMinus1264.small1265,CompactMinus1264.nodes1265,NodeMinus19.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1264.p1266,GridMinus.atNode 1266,GridMinus.atNode 1267,NodeMinus19.w50,CompactMinus1264.checked1266,CompactMinus1264.small1266,CompactMinus1264.nodes1266,NodeMinus19.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1264.p1267,GridMinus.atNode 1267,GridMinus.atNode 1268,NodeMinus19.w51,CompactMinus1264.checked1267,CompactMinus1264.small1267,CompactMinus1264.nodes1267,NodeMinus19.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1264.p1268,GridMinus.atNode 1268,GridMinus.atNode 1269,NodeMinus19.w52,CompactMinus1264.checked1268,CompactMinus1264.small1268,CompactMinus1264.nodes1268,NodeMinus19.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1264.p1269,GridMinus.atNode 1269,GridMinus.atNode 1270,NodeMinus19.w53,CompactMinus1264.checked1269,CompactMinus1264.small1269,CompactMinus1264.nodes1269,NodeMinus19.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1264.p1270,GridMinus.atNode 1270,GridMinus.atNode 1271,NodeMinus19.w54,CompactMinus1264.checked1270,CompactMinus1264.small1270,CompactMinus1264.nodes1270,NodeMinus19.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1264.p1271,GridMinus.atNode 1271,GridMinus.atNode 1272,NodeMinus19.w55,CompactMinus1264.checked1271,CompactMinus1264.small1271,CompactMinus1264.nodes1271,NodeMinus19.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1264.p1272,GridMinus.atNode 1272,GridMinus.atNode 1273,NodeMinus19.w56,CompactMinus1264.checked1272,CompactMinus1264.small1272,CompactMinus1264.nodes1272,NodeMinus19.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1264.p1273,GridMinus.atNode 1273,GridMinus.atNode 1274,NodeMinus19.w57,CompactMinus1264.checked1273,CompactMinus1264.small1273,CompactMinus1264.nodes1273,NodeMinus19.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1264.p1274,GridMinus.atNode 1274,GridMinus.atNode 1275,NodeMinus19.w58,CompactMinus1264.checked1274,CompactMinus1264.small1274,CompactMinus1264.nodes1274,NodeMinus19.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1264.p1275,GridMinus.atNode 1275,GridMinus.atNode 1276,NodeMinus19.w59,CompactMinus1264.checked1275,CompactMinus1264.small1275,CompactMinus1264.nodes1275,NodeMinus19.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1264.p1276,GridMinus.atNode 1276,GridMinus.atNode 1277,NodeMinus19.w60,CompactMinus1264.checked1276,CompactMinus1264.small1276,CompactMinus1264.nodes1276,NodeMinus19.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1264.p1277,GridMinus.atNode 1277,GridMinus.atNode 1278,NodeMinus19.w61,CompactMinus1264.checked1277,CompactMinus1264.small1277,CompactMinus1264.nodes1277,NodeMinus19.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1264.p1278,GridMinus.atNode 1278,GridMinus.atNode 1279,NodeMinus19.w62,CompactMinus1264.checked1278,CompactMinus1264.small1278,CompactMinus1264.nodes1278,NodeMinus19.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1264.p1279,GridMinus.atNode 1279,GridMinus.atNode 1280,NodeMinus19.w63,CompactMinus1264.checked1279,CompactMinus1264.small1279,CompactMinus1264.nodes1279,NodeMinus19.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (1216+j) ∧
    (atRow j).right=GridMinus.atNode (1216+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus19
