import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus1216
import SolitonClassification.Rotating.ResetPackedPlus1232
import SolitonClassification.Rotating.ResetPackedPlus1248
import SolitonClassification.Rotating.ResetPackedPlus1264
namespace SolitonClassification.Rotating.DyadicReset.TilePlus19
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus1216.p1216,GridPlus.atNode 1216,GridPlus.atNode 1217,NodePlus19.w0,CompactPlus1216.checked1216,CompactPlus1216.small1216,CompactPlus1216.nodes1216,NodePlus19.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus1216.p1217,GridPlus.atNode 1217,GridPlus.atNode 1218,NodePlus19.w1,CompactPlus1216.checked1217,CompactPlus1216.small1217,CompactPlus1216.nodes1217,NodePlus19.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus1216.p1218,GridPlus.atNode 1218,GridPlus.atNode 1219,NodePlus19.w2,CompactPlus1216.checked1218,CompactPlus1216.small1218,CompactPlus1216.nodes1218,NodePlus19.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus1216.p1219,GridPlus.atNode 1219,GridPlus.atNode 1220,NodePlus19.w3,CompactPlus1216.checked1219,CompactPlus1216.small1219,CompactPlus1216.nodes1219,NodePlus19.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus1216.p1220,GridPlus.atNode 1220,GridPlus.atNode 1221,NodePlus19.w4,CompactPlus1216.checked1220,CompactPlus1216.small1220,CompactPlus1216.nodes1220,NodePlus19.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus1216.p1221,GridPlus.atNode 1221,GridPlus.atNode 1222,NodePlus19.w5,CompactPlus1216.checked1221,CompactPlus1216.small1221,CompactPlus1216.nodes1221,NodePlus19.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus1216.p1222,GridPlus.atNode 1222,GridPlus.atNode 1223,NodePlus19.w6,CompactPlus1216.checked1222,CompactPlus1216.small1222,CompactPlus1216.nodes1222,NodePlus19.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus1216.p1223,GridPlus.atNode 1223,GridPlus.atNode 1224,NodePlus19.w7,CompactPlus1216.checked1223,CompactPlus1216.small1223,CompactPlus1216.nodes1223,NodePlus19.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus1216.p1224,GridPlus.atNode 1224,GridPlus.atNode 1225,NodePlus19.w8,CompactPlus1216.checked1224,CompactPlus1216.small1224,CompactPlus1216.nodes1224,NodePlus19.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus1216.p1225,GridPlus.atNode 1225,GridPlus.atNode 1226,NodePlus19.w9,CompactPlus1216.checked1225,CompactPlus1216.small1225,CompactPlus1216.nodes1225,NodePlus19.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus1216.p1226,GridPlus.atNode 1226,GridPlus.atNode 1227,NodePlus19.w10,CompactPlus1216.checked1226,CompactPlus1216.small1226,CompactPlus1216.nodes1226,NodePlus19.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus1216.p1227,GridPlus.atNode 1227,GridPlus.atNode 1228,NodePlus19.w11,CompactPlus1216.checked1227,CompactPlus1216.small1227,CompactPlus1216.nodes1227,NodePlus19.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus1216.p1228,GridPlus.atNode 1228,GridPlus.atNode 1229,NodePlus19.w12,CompactPlus1216.checked1228,CompactPlus1216.small1228,CompactPlus1216.nodes1228,NodePlus19.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus1216.p1229,GridPlus.atNode 1229,GridPlus.atNode 1230,NodePlus19.w13,CompactPlus1216.checked1229,CompactPlus1216.small1229,CompactPlus1216.nodes1229,NodePlus19.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus1216.p1230,GridPlus.atNode 1230,GridPlus.atNode 1231,NodePlus19.w14,CompactPlus1216.checked1230,CompactPlus1216.small1230,CompactPlus1216.nodes1230,NodePlus19.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus1216.p1231,GridPlus.atNode 1231,GridPlus.atNode 1232,NodePlus19.w15,CompactPlus1216.checked1231,CompactPlus1216.small1231,CompactPlus1216.nodes1231,NodePlus19.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus1232.p1232,GridPlus.atNode 1232,GridPlus.atNode 1233,NodePlus19.w16,CompactPlus1232.checked1232,CompactPlus1232.small1232,CompactPlus1232.nodes1232,NodePlus19.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus1232.p1233,GridPlus.atNode 1233,GridPlus.atNode 1234,NodePlus19.w17,CompactPlus1232.checked1233,CompactPlus1232.small1233,CompactPlus1232.nodes1233,NodePlus19.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus1232.p1234,GridPlus.atNode 1234,GridPlus.atNode 1235,NodePlus19.w18,CompactPlus1232.checked1234,CompactPlus1232.small1234,CompactPlus1232.nodes1234,NodePlus19.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus1232.p1235,GridPlus.atNode 1235,GridPlus.atNode 1236,NodePlus19.w19,CompactPlus1232.checked1235,CompactPlus1232.small1235,CompactPlus1232.nodes1235,NodePlus19.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus1232.p1236,GridPlus.atNode 1236,GridPlus.atNode 1237,NodePlus19.w20,CompactPlus1232.checked1236,CompactPlus1232.small1236,CompactPlus1232.nodes1236,NodePlus19.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus1232.p1237,GridPlus.atNode 1237,GridPlus.atNode 1238,NodePlus19.w21,CompactPlus1232.checked1237,CompactPlus1232.small1237,CompactPlus1232.nodes1237,NodePlus19.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus1232.p1238,GridPlus.atNode 1238,GridPlus.atNode 1239,NodePlus19.w22,CompactPlus1232.checked1238,CompactPlus1232.small1238,CompactPlus1232.nodes1238,NodePlus19.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus1232.p1239,GridPlus.atNode 1239,GridPlus.atNode 1240,NodePlus19.w23,CompactPlus1232.checked1239,CompactPlus1232.small1239,CompactPlus1232.nodes1239,NodePlus19.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus1232.p1240,GridPlus.atNode 1240,GridPlus.atNode 1241,NodePlus19.w24,CompactPlus1232.checked1240,CompactPlus1232.small1240,CompactPlus1232.nodes1240,NodePlus19.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus1232.p1241,GridPlus.atNode 1241,GridPlus.atNode 1242,NodePlus19.w25,CompactPlus1232.checked1241,CompactPlus1232.small1241,CompactPlus1232.nodes1241,NodePlus19.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus1232.p1242,GridPlus.atNode 1242,GridPlus.atNode 1243,NodePlus19.w26,CompactPlus1232.checked1242,CompactPlus1232.small1242,CompactPlus1232.nodes1242,NodePlus19.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus1232.p1243,GridPlus.atNode 1243,GridPlus.atNode 1244,NodePlus19.w27,CompactPlus1232.checked1243,CompactPlus1232.small1243,CompactPlus1232.nodes1243,NodePlus19.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus1232.p1244,GridPlus.atNode 1244,GridPlus.atNode 1245,NodePlus19.w28,CompactPlus1232.checked1244,CompactPlus1232.small1244,CompactPlus1232.nodes1244,NodePlus19.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus1232.p1245,GridPlus.atNode 1245,GridPlus.atNode 1246,NodePlus19.w29,CompactPlus1232.checked1245,CompactPlus1232.small1245,CompactPlus1232.nodes1245,NodePlus19.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus1232.p1246,GridPlus.atNode 1246,GridPlus.atNode 1247,NodePlus19.w30,CompactPlus1232.checked1246,CompactPlus1232.small1246,CompactPlus1232.nodes1246,NodePlus19.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus1232.p1247,GridPlus.atNode 1247,GridPlus.atNode 1248,NodePlus19.w31,CompactPlus1232.checked1247,CompactPlus1232.small1247,CompactPlus1232.nodes1247,NodePlus19.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus1248.p1248,GridPlus.atNode 1248,GridPlus.atNode 1249,NodePlus19.w32,CompactPlus1248.checked1248,CompactPlus1248.small1248,CompactPlus1248.nodes1248,NodePlus19.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus1248.p1249,GridPlus.atNode 1249,GridPlus.atNode 1250,NodePlus19.w33,CompactPlus1248.checked1249,CompactPlus1248.small1249,CompactPlus1248.nodes1249,NodePlus19.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus1248.p1250,GridPlus.atNode 1250,GridPlus.atNode 1251,NodePlus19.w34,CompactPlus1248.checked1250,CompactPlus1248.small1250,CompactPlus1248.nodes1250,NodePlus19.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus1248.p1251,GridPlus.atNode 1251,GridPlus.atNode 1252,NodePlus19.w35,CompactPlus1248.checked1251,CompactPlus1248.small1251,CompactPlus1248.nodes1251,NodePlus19.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus1248.p1252,GridPlus.atNode 1252,GridPlus.atNode 1253,NodePlus19.w36,CompactPlus1248.checked1252,CompactPlus1248.small1252,CompactPlus1248.nodes1252,NodePlus19.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus1248.p1253,GridPlus.atNode 1253,GridPlus.atNode 1254,NodePlus19.w37,CompactPlus1248.checked1253,CompactPlus1248.small1253,CompactPlus1248.nodes1253,NodePlus19.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus1248.p1254,GridPlus.atNode 1254,GridPlus.atNode 1255,NodePlus19.w38,CompactPlus1248.checked1254,CompactPlus1248.small1254,CompactPlus1248.nodes1254,NodePlus19.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus1248.p1255,GridPlus.atNode 1255,GridPlus.atNode 1256,NodePlus19.w39,CompactPlus1248.checked1255,CompactPlus1248.small1255,CompactPlus1248.nodes1255,NodePlus19.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus1248.p1256,GridPlus.atNode 1256,GridPlus.atNode 1257,NodePlus19.w40,CompactPlus1248.checked1256,CompactPlus1248.small1256,CompactPlus1248.nodes1256,NodePlus19.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus1248.p1257,GridPlus.atNode 1257,GridPlus.atNode 1258,NodePlus19.w41,CompactPlus1248.checked1257,CompactPlus1248.small1257,CompactPlus1248.nodes1257,NodePlus19.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus1248.p1258,GridPlus.atNode 1258,GridPlus.atNode 1259,NodePlus19.w42,CompactPlus1248.checked1258,CompactPlus1248.small1258,CompactPlus1248.nodes1258,NodePlus19.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus1248.p1259,GridPlus.atNode 1259,GridPlus.atNode 1260,NodePlus19.w43,CompactPlus1248.checked1259,CompactPlus1248.small1259,CompactPlus1248.nodes1259,NodePlus19.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus1248.p1260,GridPlus.atNode 1260,GridPlus.atNode 1261,NodePlus19.w44,CompactPlus1248.checked1260,CompactPlus1248.small1260,CompactPlus1248.nodes1260,NodePlus19.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus1248.p1261,GridPlus.atNode 1261,GridPlus.atNode 1262,NodePlus19.w45,CompactPlus1248.checked1261,CompactPlus1248.small1261,CompactPlus1248.nodes1261,NodePlus19.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus1248.p1262,GridPlus.atNode 1262,GridPlus.atNode 1263,NodePlus19.w46,CompactPlus1248.checked1262,CompactPlus1248.small1262,CompactPlus1248.nodes1262,NodePlus19.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus1248.p1263,GridPlus.atNode 1263,GridPlus.atNode 1264,NodePlus19.w47,CompactPlus1248.checked1263,CompactPlus1248.small1263,CompactPlus1248.nodes1263,NodePlus19.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus1264.p1264,GridPlus.atNode 1264,GridPlus.atNode 1265,NodePlus19.w48,CompactPlus1264.checked1264,CompactPlus1264.small1264,CompactPlus1264.nodes1264,NodePlus19.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus1264.p1265,GridPlus.atNode 1265,GridPlus.atNode 1266,NodePlus19.w49,CompactPlus1264.checked1265,CompactPlus1264.small1265,CompactPlus1264.nodes1265,NodePlus19.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus1264.p1266,GridPlus.atNode 1266,GridPlus.atNode 1267,NodePlus19.w50,CompactPlus1264.checked1266,CompactPlus1264.small1266,CompactPlus1264.nodes1266,NodePlus19.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus1264.p1267,GridPlus.atNode 1267,GridPlus.atNode 1268,NodePlus19.w51,CompactPlus1264.checked1267,CompactPlus1264.small1267,CompactPlus1264.nodes1267,NodePlus19.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus1264.p1268,GridPlus.atNode 1268,GridPlus.atNode 1269,NodePlus19.w52,CompactPlus1264.checked1268,CompactPlus1264.small1268,CompactPlus1264.nodes1268,NodePlus19.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus1264.p1269,GridPlus.atNode 1269,GridPlus.atNode 1270,NodePlus19.w53,CompactPlus1264.checked1269,CompactPlus1264.small1269,CompactPlus1264.nodes1269,NodePlus19.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus1264.p1270,GridPlus.atNode 1270,GridPlus.atNode 1271,NodePlus19.w54,CompactPlus1264.checked1270,CompactPlus1264.small1270,CompactPlus1264.nodes1270,NodePlus19.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus1264.p1271,GridPlus.atNode 1271,GridPlus.atNode 1272,NodePlus19.w55,CompactPlus1264.checked1271,CompactPlus1264.small1271,CompactPlus1264.nodes1271,NodePlus19.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus1264.p1272,GridPlus.atNode 1272,GridPlus.atNode 1273,NodePlus19.w56,CompactPlus1264.checked1272,CompactPlus1264.small1272,CompactPlus1264.nodes1272,NodePlus19.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus1264.p1273,GridPlus.atNode 1273,GridPlus.atNode 1274,NodePlus19.w57,CompactPlus1264.checked1273,CompactPlus1264.small1273,CompactPlus1264.nodes1273,NodePlus19.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus1264.p1274,GridPlus.atNode 1274,GridPlus.atNode 1275,NodePlus19.w58,CompactPlus1264.checked1274,CompactPlus1264.small1274,CompactPlus1264.nodes1274,NodePlus19.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus1264.p1275,GridPlus.atNode 1275,GridPlus.atNode 1276,NodePlus19.w59,CompactPlus1264.checked1275,CompactPlus1264.small1275,CompactPlus1264.nodes1275,NodePlus19.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus1264.p1276,GridPlus.atNode 1276,GridPlus.atNode 1277,NodePlus19.w60,CompactPlus1264.checked1276,CompactPlus1264.small1276,CompactPlus1264.nodes1276,NodePlus19.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus1264.p1277,GridPlus.atNode 1277,GridPlus.atNode 1278,NodePlus19.w61,CompactPlus1264.checked1277,CompactPlus1264.small1277,CompactPlus1264.nodes1277,NodePlus19.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus1264.p1278,GridPlus.atNode 1278,GridPlus.atNode 1279,NodePlus19.w62,CompactPlus1264.checked1278,CompactPlus1264.small1278,CompactPlus1264.nodes1278,NodePlus19.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus1264.p1279,GridPlus.atNode 1279,GridPlus.atNode 1280,NodePlus19.w63,CompactPlus1264.checked1279,CompactPlus1264.small1279,CompactPlus1264.nodes1279,NodePlus19.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (1216+j) ∧
    (atRow j).right=GridPlus.atNode (1216+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus19
