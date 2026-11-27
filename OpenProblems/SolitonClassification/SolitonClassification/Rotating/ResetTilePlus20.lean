import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus1280
import SolitonClassification.Rotating.ResetPackedPlus1296
import SolitonClassification.Rotating.ResetPackedPlus1312
import SolitonClassification.Rotating.ResetPackedPlus1328
namespace SolitonClassification.Rotating.DyadicReset.TilePlus20
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus1280.p1280,GridPlus.atNode 1280,GridPlus.atNode 1281,NodePlus20.w0,CompactPlus1280.checked1280,CompactPlus1280.small1280,CompactPlus1280.nodes1280,NodePlus20.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus1280.p1281,GridPlus.atNode 1281,GridPlus.atNode 1282,NodePlus20.w1,CompactPlus1280.checked1281,CompactPlus1280.small1281,CompactPlus1280.nodes1281,NodePlus20.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus1280.p1282,GridPlus.atNode 1282,GridPlus.atNode 1283,NodePlus20.w2,CompactPlus1280.checked1282,CompactPlus1280.small1282,CompactPlus1280.nodes1282,NodePlus20.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus1280.p1283,GridPlus.atNode 1283,GridPlus.atNode 1284,NodePlus20.w3,CompactPlus1280.checked1283,CompactPlus1280.small1283,CompactPlus1280.nodes1283,NodePlus20.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus1280.p1284,GridPlus.atNode 1284,GridPlus.atNode 1285,NodePlus20.w4,CompactPlus1280.checked1284,CompactPlus1280.small1284,CompactPlus1280.nodes1284,NodePlus20.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus1280.p1285,GridPlus.atNode 1285,GridPlus.atNode 1286,NodePlus20.w5,CompactPlus1280.checked1285,CompactPlus1280.small1285,CompactPlus1280.nodes1285,NodePlus20.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus1280.p1286,GridPlus.atNode 1286,GridPlus.atNode 1287,NodePlus20.w6,CompactPlus1280.checked1286,CompactPlus1280.small1286,CompactPlus1280.nodes1286,NodePlus20.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus1280.p1287,GridPlus.atNode 1287,GridPlus.atNode 1288,NodePlus20.w7,CompactPlus1280.checked1287,CompactPlus1280.small1287,CompactPlus1280.nodes1287,NodePlus20.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus1280.p1288,GridPlus.atNode 1288,GridPlus.atNode 1289,NodePlus20.w8,CompactPlus1280.checked1288,CompactPlus1280.small1288,CompactPlus1280.nodes1288,NodePlus20.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus1280.p1289,GridPlus.atNode 1289,GridPlus.atNode 1290,NodePlus20.w9,CompactPlus1280.checked1289,CompactPlus1280.small1289,CompactPlus1280.nodes1289,NodePlus20.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus1280.p1290,GridPlus.atNode 1290,GridPlus.atNode 1291,NodePlus20.w10,CompactPlus1280.checked1290,CompactPlus1280.small1290,CompactPlus1280.nodes1290,NodePlus20.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus1280.p1291,GridPlus.atNode 1291,GridPlus.atNode 1292,NodePlus20.w11,CompactPlus1280.checked1291,CompactPlus1280.small1291,CompactPlus1280.nodes1291,NodePlus20.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus1280.p1292,GridPlus.atNode 1292,GridPlus.atNode 1293,NodePlus20.w12,CompactPlus1280.checked1292,CompactPlus1280.small1292,CompactPlus1280.nodes1292,NodePlus20.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus1280.p1293,GridPlus.atNode 1293,GridPlus.atNode 1294,NodePlus20.w13,CompactPlus1280.checked1293,CompactPlus1280.small1293,CompactPlus1280.nodes1293,NodePlus20.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus1280.p1294,GridPlus.atNode 1294,GridPlus.atNode 1295,NodePlus20.w14,CompactPlus1280.checked1294,CompactPlus1280.small1294,CompactPlus1280.nodes1294,NodePlus20.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus1280.p1295,GridPlus.atNode 1295,GridPlus.atNode 1296,NodePlus20.w15,CompactPlus1280.checked1295,CompactPlus1280.small1295,CompactPlus1280.nodes1295,NodePlus20.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus1296.p1296,GridPlus.atNode 1296,GridPlus.atNode 1297,NodePlus20.w16,CompactPlus1296.checked1296,CompactPlus1296.small1296,CompactPlus1296.nodes1296,NodePlus20.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus1296.p1297,GridPlus.atNode 1297,GridPlus.atNode 1298,NodePlus20.w17,CompactPlus1296.checked1297,CompactPlus1296.small1297,CompactPlus1296.nodes1297,NodePlus20.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus1296.p1298,GridPlus.atNode 1298,GridPlus.atNode 1299,NodePlus20.w18,CompactPlus1296.checked1298,CompactPlus1296.small1298,CompactPlus1296.nodes1298,NodePlus20.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus1296.p1299,GridPlus.atNode 1299,GridPlus.atNode 1300,NodePlus20.w19,CompactPlus1296.checked1299,CompactPlus1296.small1299,CompactPlus1296.nodes1299,NodePlus20.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus1296.p1300,GridPlus.atNode 1300,GridPlus.atNode 1301,NodePlus20.w20,CompactPlus1296.checked1300,CompactPlus1296.small1300,CompactPlus1296.nodes1300,NodePlus20.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus1296.p1301,GridPlus.atNode 1301,GridPlus.atNode 1302,NodePlus20.w21,CompactPlus1296.checked1301,CompactPlus1296.small1301,CompactPlus1296.nodes1301,NodePlus20.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus1296.p1302,GridPlus.atNode 1302,GridPlus.atNode 1303,NodePlus20.w22,CompactPlus1296.checked1302,CompactPlus1296.small1302,CompactPlus1296.nodes1302,NodePlus20.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus1296.p1303,GridPlus.atNode 1303,GridPlus.atNode 1304,NodePlus20.w23,CompactPlus1296.checked1303,CompactPlus1296.small1303,CompactPlus1296.nodes1303,NodePlus20.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus1296.p1304,GridPlus.atNode 1304,GridPlus.atNode 1305,NodePlus20.w24,CompactPlus1296.checked1304,CompactPlus1296.small1304,CompactPlus1296.nodes1304,NodePlus20.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus1296.p1305,GridPlus.atNode 1305,GridPlus.atNode 1306,NodePlus20.w25,CompactPlus1296.checked1305,CompactPlus1296.small1305,CompactPlus1296.nodes1305,NodePlus20.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus1296.p1306,GridPlus.atNode 1306,GridPlus.atNode 1307,NodePlus20.w26,CompactPlus1296.checked1306,CompactPlus1296.small1306,CompactPlus1296.nodes1306,NodePlus20.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus1296.p1307,GridPlus.atNode 1307,GridPlus.atNode 1308,NodePlus20.w27,CompactPlus1296.checked1307,CompactPlus1296.small1307,CompactPlus1296.nodes1307,NodePlus20.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus1296.p1308,GridPlus.atNode 1308,GridPlus.atNode 1309,NodePlus20.w28,CompactPlus1296.checked1308,CompactPlus1296.small1308,CompactPlus1296.nodes1308,NodePlus20.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus1296.p1309,GridPlus.atNode 1309,GridPlus.atNode 1310,NodePlus20.w29,CompactPlus1296.checked1309,CompactPlus1296.small1309,CompactPlus1296.nodes1309,NodePlus20.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus1296.p1310,GridPlus.atNode 1310,GridPlus.atNode 1311,NodePlus20.w30,CompactPlus1296.checked1310,CompactPlus1296.small1310,CompactPlus1296.nodes1310,NodePlus20.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus1296.p1311,GridPlus.atNode 1311,GridPlus.atNode 1312,NodePlus20.w31,CompactPlus1296.checked1311,CompactPlus1296.small1311,CompactPlus1296.nodes1311,NodePlus20.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus1312.p1312,GridPlus.atNode 1312,GridPlus.atNode 1313,NodePlus20.w32,CompactPlus1312.checked1312,CompactPlus1312.small1312,CompactPlus1312.nodes1312,NodePlus20.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus1312.p1313,GridPlus.atNode 1313,GridPlus.atNode 1314,NodePlus20.w33,CompactPlus1312.checked1313,CompactPlus1312.small1313,CompactPlus1312.nodes1313,NodePlus20.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus1312.p1314,GridPlus.atNode 1314,GridPlus.atNode 1315,NodePlus20.w34,CompactPlus1312.checked1314,CompactPlus1312.small1314,CompactPlus1312.nodes1314,NodePlus20.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus1312.p1315,GridPlus.atNode 1315,GridPlus.atNode 1316,NodePlus20.w35,CompactPlus1312.checked1315,CompactPlus1312.small1315,CompactPlus1312.nodes1315,NodePlus20.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus1312.p1316,GridPlus.atNode 1316,GridPlus.atNode 1317,NodePlus20.w36,CompactPlus1312.checked1316,CompactPlus1312.small1316,CompactPlus1312.nodes1316,NodePlus20.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus1312.p1317,GridPlus.atNode 1317,GridPlus.atNode 1318,NodePlus20.w37,CompactPlus1312.checked1317,CompactPlus1312.small1317,CompactPlus1312.nodes1317,NodePlus20.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus1312.p1318,GridPlus.atNode 1318,GridPlus.atNode 1319,NodePlus20.w38,CompactPlus1312.checked1318,CompactPlus1312.small1318,CompactPlus1312.nodes1318,NodePlus20.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus1312.p1319,GridPlus.atNode 1319,GridPlus.atNode 1320,NodePlus20.w39,CompactPlus1312.checked1319,CompactPlus1312.small1319,CompactPlus1312.nodes1319,NodePlus20.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus1312.p1320,GridPlus.atNode 1320,GridPlus.atNode 1321,NodePlus20.w40,CompactPlus1312.checked1320,CompactPlus1312.small1320,CompactPlus1312.nodes1320,NodePlus20.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus1312.p1321,GridPlus.atNode 1321,GridPlus.atNode 1322,NodePlus20.w41,CompactPlus1312.checked1321,CompactPlus1312.small1321,CompactPlus1312.nodes1321,NodePlus20.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus1312.p1322,GridPlus.atNode 1322,GridPlus.atNode 1323,NodePlus20.w42,CompactPlus1312.checked1322,CompactPlus1312.small1322,CompactPlus1312.nodes1322,NodePlus20.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus1312.p1323,GridPlus.atNode 1323,GridPlus.atNode 1324,NodePlus20.w43,CompactPlus1312.checked1323,CompactPlus1312.small1323,CompactPlus1312.nodes1323,NodePlus20.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus1312.p1324,GridPlus.atNode 1324,GridPlus.atNode 1325,NodePlus20.w44,CompactPlus1312.checked1324,CompactPlus1312.small1324,CompactPlus1312.nodes1324,NodePlus20.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus1312.p1325,GridPlus.atNode 1325,GridPlus.atNode 1326,NodePlus20.w45,CompactPlus1312.checked1325,CompactPlus1312.small1325,CompactPlus1312.nodes1325,NodePlus20.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus1312.p1326,GridPlus.atNode 1326,GridPlus.atNode 1327,NodePlus20.w46,CompactPlus1312.checked1326,CompactPlus1312.small1326,CompactPlus1312.nodes1326,NodePlus20.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus1312.p1327,GridPlus.atNode 1327,GridPlus.atNode 1328,NodePlus20.w47,CompactPlus1312.checked1327,CompactPlus1312.small1327,CompactPlus1312.nodes1327,NodePlus20.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus1328.p1328,GridPlus.atNode 1328,GridPlus.atNode 1329,NodePlus20.w48,CompactPlus1328.checked1328,CompactPlus1328.small1328,CompactPlus1328.nodes1328,NodePlus20.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus1328.p1329,GridPlus.atNode 1329,GridPlus.atNode 1330,NodePlus20.w49,CompactPlus1328.checked1329,CompactPlus1328.small1329,CompactPlus1328.nodes1329,NodePlus20.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus1328.p1330,GridPlus.atNode 1330,GridPlus.atNode 1331,NodePlus20.w50,CompactPlus1328.checked1330,CompactPlus1328.small1330,CompactPlus1328.nodes1330,NodePlus20.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus1328.p1331,GridPlus.atNode 1331,GridPlus.atNode 1332,NodePlus20.w51,CompactPlus1328.checked1331,CompactPlus1328.small1331,CompactPlus1328.nodes1331,NodePlus20.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus1328.p1332,GridPlus.atNode 1332,GridPlus.atNode 1333,NodePlus20.w52,CompactPlus1328.checked1332,CompactPlus1328.small1332,CompactPlus1328.nodes1332,NodePlus20.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus1328.p1333,GridPlus.atNode 1333,GridPlus.atNode 1334,NodePlus20.w53,CompactPlus1328.checked1333,CompactPlus1328.small1333,CompactPlus1328.nodes1333,NodePlus20.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus1328.p1334,GridPlus.atNode 1334,GridPlus.atNode 1335,NodePlus20.w54,CompactPlus1328.checked1334,CompactPlus1328.small1334,CompactPlus1328.nodes1334,NodePlus20.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus1328.p1335,GridPlus.atNode 1335,GridPlus.atNode 1336,NodePlus20.w55,CompactPlus1328.checked1335,CompactPlus1328.small1335,CompactPlus1328.nodes1335,NodePlus20.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus1328.p1336,GridPlus.atNode 1336,GridPlus.atNode 1337,NodePlus20.w56,CompactPlus1328.checked1336,CompactPlus1328.small1336,CompactPlus1328.nodes1336,NodePlus20.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus1328.p1337,GridPlus.atNode 1337,GridPlus.atNode 1338,NodePlus20.w57,CompactPlus1328.checked1337,CompactPlus1328.small1337,CompactPlus1328.nodes1337,NodePlus20.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus1328.p1338,GridPlus.atNode 1338,GridPlus.atNode 1339,NodePlus20.w58,CompactPlus1328.checked1338,CompactPlus1328.small1338,CompactPlus1328.nodes1338,NodePlus20.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus1328.p1339,GridPlus.atNode 1339,GridPlus.atNode 1340,NodePlus20.w59,CompactPlus1328.checked1339,CompactPlus1328.small1339,CompactPlus1328.nodes1339,NodePlus20.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus1328.p1340,GridPlus.atNode 1340,GridPlus.atNode 1341,NodePlus20.w60,CompactPlus1328.checked1340,CompactPlus1328.small1340,CompactPlus1328.nodes1340,NodePlus20.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus1328.p1341,GridPlus.atNode 1341,GridPlus.atNode 1342,NodePlus20.w61,CompactPlus1328.checked1341,CompactPlus1328.small1341,CompactPlus1328.nodes1341,NodePlus20.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus1328.p1342,GridPlus.atNode 1342,GridPlus.atNode 1343,NodePlus20.w62,CompactPlus1328.checked1342,CompactPlus1328.small1342,CompactPlus1328.nodes1342,NodePlus20.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus1328.p1343,GridPlus.atNode 1343,GridPlus.atNode 1344,NodePlus20.w63,CompactPlus1328.checked1343,CompactPlus1328.small1343,CompactPlus1328.nodes1343,NodePlus20.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (1280+j) ∧
    (atRow j).right=GridPlus.atNode (1280+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus20
