import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus1280
import SolitonClassification.Rotating.ResetPackedMinus1296
import SolitonClassification.Rotating.ResetPackedMinus1312
import SolitonClassification.Rotating.ResetPackedMinus1328
namespace SolitonClassification.Rotating.DyadicReset.TileMinus20
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1280.p1280,GridMinus.atNode 1280,GridMinus.atNode 1281,NodeMinus20.w0,CompactMinus1280.checked1280,CompactMinus1280.small1280,CompactMinus1280.nodes1280,NodeMinus20.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1280.p1281,GridMinus.atNode 1281,GridMinus.atNode 1282,NodeMinus20.w1,CompactMinus1280.checked1281,CompactMinus1280.small1281,CompactMinus1280.nodes1281,NodeMinus20.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1280.p1282,GridMinus.atNode 1282,GridMinus.atNode 1283,NodeMinus20.w2,CompactMinus1280.checked1282,CompactMinus1280.small1282,CompactMinus1280.nodes1282,NodeMinus20.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1280.p1283,GridMinus.atNode 1283,GridMinus.atNode 1284,NodeMinus20.w3,CompactMinus1280.checked1283,CompactMinus1280.small1283,CompactMinus1280.nodes1283,NodeMinus20.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1280.p1284,GridMinus.atNode 1284,GridMinus.atNode 1285,NodeMinus20.w4,CompactMinus1280.checked1284,CompactMinus1280.small1284,CompactMinus1280.nodes1284,NodeMinus20.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1280.p1285,GridMinus.atNode 1285,GridMinus.atNode 1286,NodeMinus20.w5,CompactMinus1280.checked1285,CompactMinus1280.small1285,CompactMinus1280.nodes1285,NodeMinus20.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1280.p1286,GridMinus.atNode 1286,GridMinus.atNode 1287,NodeMinus20.w6,CompactMinus1280.checked1286,CompactMinus1280.small1286,CompactMinus1280.nodes1286,NodeMinus20.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1280.p1287,GridMinus.atNode 1287,GridMinus.atNode 1288,NodeMinus20.w7,CompactMinus1280.checked1287,CompactMinus1280.small1287,CompactMinus1280.nodes1287,NodeMinus20.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1280.p1288,GridMinus.atNode 1288,GridMinus.atNode 1289,NodeMinus20.w8,CompactMinus1280.checked1288,CompactMinus1280.small1288,CompactMinus1280.nodes1288,NodeMinus20.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1280.p1289,GridMinus.atNode 1289,GridMinus.atNode 1290,NodeMinus20.w9,CompactMinus1280.checked1289,CompactMinus1280.small1289,CompactMinus1280.nodes1289,NodeMinus20.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1280.p1290,GridMinus.atNode 1290,GridMinus.atNode 1291,NodeMinus20.w10,CompactMinus1280.checked1290,CompactMinus1280.small1290,CompactMinus1280.nodes1290,NodeMinus20.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1280.p1291,GridMinus.atNode 1291,GridMinus.atNode 1292,NodeMinus20.w11,CompactMinus1280.checked1291,CompactMinus1280.small1291,CompactMinus1280.nodes1291,NodeMinus20.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1280.p1292,GridMinus.atNode 1292,GridMinus.atNode 1293,NodeMinus20.w12,CompactMinus1280.checked1292,CompactMinus1280.small1292,CompactMinus1280.nodes1292,NodeMinus20.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1280.p1293,GridMinus.atNode 1293,GridMinus.atNode 1294,NodeMinus20.w13,CompactMinus1280.checked1293,CompactMinus1280.small1293,CompactMinus1280.nodes1293,NodeMinus20.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1280.p1294,GridMinus.atNode 1294,GridMinus.atNode 1295,NodeMinus20.w14,CompactMinus1280.checked1294,CompactMinus1280.small1294,CompactMinus1280.nodes1294,NodeMinus20.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1280.p1295,GridMinus.atNode 1295,GridMinus.atNode 1296,NodeMinus20.w15,CompactMinus1280.checked1295,CompactMinus1280.small1295,CompactMinus1280.nodes1295,NodeMinus20.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1296.p1296,GridMinus.atNode 1296,GridMinus.atNode 1297,NodeMinus20.w16,CompactMinus1296.checked1296,CompactMinus1296.small1296,CompactMinus1296.nodes1296,NodeMinus20.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1296.p1297,GridMinus.atNode 1297,GridMinus.atNode 1298,NodeMinus20.w17,CompactMinus1296.checked1297,CompactMinus1296.small1297,CompactMinus1296.nodes1297,NodeMinus20.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1296.p1298,GridMinus.atNode 1298,GridMinus.atNode 1299,NodeMinus20.w18,CompactMinus1296.checked1298,CompactMinus1296.small1298,CompactMinus1296.nodes1298,NodeMinus20.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1296.p1299,GridMinus.atNode 1299,GridMinus.atNode 1300,NodeMinus20.w19,CompactMinus1296.checked1299,CompactMinus1296.small1299,CompactMinus1296.nodes1299,NodeMinus20.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1296.p1300,GridMinus.atNode 1300,GridMinus.atNode 1301,NodeMinus20.w20,CompactMinus1296.checked1300,CompactMinus1296.small1300,CompactMinus1296.nodes1300,NodeMinus20.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1296.p1301,GridMinus.atNode 1301,GridMinus.atNode 1302,NodeMinus20.w21,CompactMinus1296.checked1301,CompactMinus1296.small1301,CompactMinus1296.nodes1301,NodeMinus20.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1296.p1302,GridMinus.atNode 1302,GridMinus.atNode 1303,NodeMinus20.w22,CompactMinus1296.checked1302,CompactMinus1296.small1302,CompactMinus1296.nodes1302,NodeMinus20.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1296.p1303,GridMinus.atNode 1303,GridMinus.atNode 1304,NodeMinus20.w23,CompactMinus1296.checked1303,CompactMinus1296.small1303,CompactMinus1296.nodes1303,NodeMinus20.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1296.p1304,GridMinus.atNode 1304,GridMinus.atNode 1305,NodeMinus20.w24,CompactMinus1296.checked1304,CompactMinus1296.small1304,CompactMinus1296.nodes1304,NodeMinus20.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1296.p1305,GridMinus.atNode 1305,GridMinus.atNode 1306,NodeMinus20.w25,CompactMinus1296.checked1305,CompactMinus1296.small1305,CompactMinus1296.nodes1305,NodeMinus20.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1296.p1306,GridMinus.atNode 1306,GridMinus.atNode 1307,NodeMinus20.w26,CompactMinus1296.checked1306,CompactMinus1296.small1306,CompactMinus1296.nodes1306,NodeMinus20.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1296.p1307,GridMinus.atNode 1307,GridMinus.atNode 1308,NodeMinus20.w27,CompactMinus1296.checked1307,CompactMinus1296.small1307,CompactMinus1296.nodes1307,NodeMinus20.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1296.p1308,GridMinus.atNode 1308,GridMinus.atNode 1309,NodeMinus20.w28,CompactMinus1296.checked1308,CompactMinus1296.small1308,CompactMinus1296.nodes1308,NodeMinus20.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1296.p1309,GridMinus.atNode 1309,GridMinus.atNode 1310,NodeMinus20.w29,CompactMinus1296.checked1309,CompactMinus1296.small1309,CompactMinus1296.nodes1309,NodeMinus20.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1296.p1310,GridMinus.atNode 1310,GridMinus.atNode 1311,NodeMinus20.w30,CompactMinus1296.checked1310,CompactMinus1296.small1310,CompactMinus1296.nodes1310,NodeMinus20.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1296.p1311,GridMinus.atNode 1311,GridMinus.atNode 1312,NodeMinus20.w31,CompactMinus1296.checked1311,CompactMinus1296.small1311,CompactMinus1296.nodes1311,NodeMinus20.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1312.p1312,GridMinus.atNode 1312,GridMinus.atNode 1313,NodeMinus20.w32,CompactMinus1312.checked1312,CompactMinus1312.small1312,CompactMinus1312.nodes1312,NodeMinus20.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1312.p1313,GridMinus.atNode 1313,GridMinus.atNode 1314,NodeMinus20.w33,CompactMinus1312.checked1313,CompactMinus1312.small1313,CompactMinus1312.nodes1313,NodeMinus20.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1312.p1314,GridMinus.atNode 1314,GridMinus.atNode 1315,NodeMinus20.w34,CompactMinus1312.checked1314,CompactMinus1312.small1314,CompactMinus1312.nodes1314,NodeMinus20.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1312.p1315,GridMinus.atNode 1315,GridMinus.atNode 1316,NodeMinus20.w35,CompactMinus1312.checked1315,CompactMinus1312.small1315,CompactMinus1312.nodes1315,NodeMinus20.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1312.p1316,GridMinus.atNode 1316,GridMinus.atNode 1317,NodeMinus20.w36,CompactMinus1312.checked1316,CompactMinus1312.small1316,CompactMinus1312.nodes1316,NodeMinus20.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1312.p1317,GridMinus.atNode 1317,GridMinus.atNode 1318,NodeMinus20.w37,CompactMinus1312.checked1317,CompactMinus1312.small1317,CompactMinus1312.nodes1317,NodeMinus20.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1312.p1318,GridMinus.atNode 1318,GridMinus.atNode 1319,NodeMinus20.w38,CompactMinus1312.checked1318,CompactMinus1312.small1318,CompactMinus1312.nodes1318,NodeMinus20.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1312.p1319,GridMinus.atNode 1319,GridMinus.atNode 1320,NodeMinus20.w39,CompactMinus1312.checked1319,CompactMinus1312.small1319,CompactMinus1312.nodes1319,NodeMinus20.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1312.p1320,GridMinus.atNode 1320,GridMinus.atNode 1321,NodeMinus20.w40,CompactMinus1312.checked1320,CompactMinus1312.small1320,CompactMinus1312.nodes1320,NodeMinus20.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1312.p1321,GridMinus.atNode 1321,GridMinus.atNode 1322,NodeMinus20.w41,CompactMinus1312.checked1321,CompactMinus1312.small1321,CompactMinus1312.nodes1321,NodeMinus20.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1312.p1322,GridMinus.atNode 1322,GridMinus.atNode 1323,NodeMinus20.w42,CompactMinus1312.checked1322,CompactMinus1312.small1322,CompactMinus1312.nodes1322,NodeMinus20.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1312.p1323,GridMinus.atNode 1323,GridMinus.atNode 1324,NodeMinus20.w43,CompactMinus1312.checked1323,CompactMinus1312.small1323,CompactMinus1312.nodes1323,NodeMinus20.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1312.p1324,GridMinus.atNode 1324,GridMinus.atNode 1325,NodeMinus20.w44,CompactMinus1312.checked1324,CompactMinus1312.small1324,CompactMinus1312.nodes1324,NodeMinus20.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1312.p1325,GridMinus.atNode 1325,GridMinus.atNode 1326,NodeMinus20.w45,CompactMinus1312.checked1325,CompactMinus1312.small1325,CompactMinus1312.nodes1325,NodeMinus20.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1312.p1326,GridMinus.atNode 1326,GridMinus.atNode 1327,NodeMinus20.w46,CompactMinus1312.checked1326,CompactMinus1312.small1326,CompactMinus1312.nodes1326,NodeMinus20.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1312.p1327,GridMinus.atNode 1327,GridMinus.atNode 1328,NodeMinus20.w47,CompactMinus1312.checked1327,CompactMinus1312.small1327,CompactMinus1312.nodes1327,NodeMinus20.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1328.p1328,GridMinus.atNode 1328,GridMinus.atNode 1329,NodeMinus20.w48,CompactMinus1328.checked1328,CompactMinus1328.small1328,CompactMinus1328.nodes1328,NodeMinus20.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1328.p1329,GridMinus.atNode 1329,GridMinus.atNode 1330,NodeMinus20.w49,CompactMinus1328.checked1329,CompactMinus1328.small1329,CompactMinus1328.nodes1329,NodeMinus20.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1328.p1330,GridMinus.atNode 1330,GridMinus.atNode 1331,NodeMinus20.w50,CompactMinus1328.checked1330,CompactMinus1328.small1330,CompactMinus1328.nodes1330,NodeMinus20.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1328.p1331,GridMinus.atNode 1331,GridMinus.atNode 1332,NodeMinus20.w51,CompactMinus1328.checked1331,CompactMinus1328.small1331,CompactMinus1328.nodes1331,NodeMinus20.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1328.p1332,GridMinus.atNode 1332,GridMinus.atNode 1333,NodeMinus20.w52,CompactMinus1328.checked1332,CompactMinus1328.small1332,CompactMinus1328.nodes1332,NodeMinus20.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1328.p1333,GridMinus.atNode 1333,GridMinus.atNode 1334,NodeMinus20.w53,CompactMinus1328.checked1333,CompactMinus1328.small1333,CompactMinus1328.nodes1333,NodeMinus20.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1328.p1334,GridMinus.atNode 1334,GridMinus.atNode 1335,NodeMinus20.w54,CompactMinus1328.checked1334,CompactMinus1328.small1334,CompactMinus1328.nodes1334,NodeMinus20.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1328.p1335,GridMinus.atNode 1335,GridMinus.atNode 1336,NodeMinus20.w55,CompactMinus1328.checked1335,CompactMinus1328.small1335,CompactMinus1328.nodes1335,NodeMinus20.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1328.p1336,GridMinus.atNode 1336,GridMinus.atNode 1337,NodeMinus20.w56,CompactMinus1328.checked1336,CompactMinus1328.small1336,CompactMinus1328.nodes1336,NodeMinus20.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1328.p1337,GridMinus.atNode 1337,GridMinus.atNode 1338,NodeMinus20.w57,CompactMinus1328.checked1337,CompactMinus1328.small1337,CompactMinus1328.nodes1337,NodeMinus20.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1328.p1338,GridMinus.atNode 1338,GridMinus.atNode 1339,NodeMinus20.w58,CompactMinus1328.checked1338,CompactMinus1328.small1338,CompactMinus1328.nodes1338,NodeMinus20.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1328.p1339,GridMinus.atNode 1339,GridMinus.atNode 1340,NodeMinus20.w59,CompactMinus1328.checked1339,CompactMinus1328.small1339,CompactMinus1328.nodes1339,NodeMinus20.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1328.p1340,GridMinus.atNode 1340,GridMinus.atNode 1341,NodeMinus20.w60,CompactMinus1328.checked1340,CompactMinus1328.small1340,CompactMinus1328.nodes1340,NodeMinus20.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1328.p1341,GridMinus.atNode 1341,GridMinus.atNode 1342,NodeMinus20.w61,CompactMinus1328.checked1341,CompactMinus1328.small1341,CompactMinus1328.nodes1341,NodeMinus20.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1328.p1342,GridMinus.atNode 1342,GridMinus.atNode 1343,NodeMinus20.w62,CompactMinus1328.checked1342,CompactMinus1328.small1342,CompactMinus1328.nodes1342,NodeMinus20.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1328.p1343,GridMinus.atNode 1343,GridMinus.atNode 1344,NodeMinus20.w63,CompactMinus1328.checked1343,CompactMinus1328.small1343,CompactMinus1328.nodes1343,NodeMinus20.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (1280+j) ∧
    (atRow j).right=GridMinus.atNode (1280+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus20
