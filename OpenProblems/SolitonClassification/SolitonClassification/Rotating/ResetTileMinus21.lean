import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus1344
import SolitonClassification.Rotating.ResetPackedMinus1360
import SolitonClassification.Rotating.ResetPackedMinus1376
import SolitonClassification.Rotating.ResetPackedMinus1392
namespace SolitonClassification.Rotating.DyadicReset.TileMinus21
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1344.p1344,GridMinus.atNode 1344,GridMinus.atNode 1345,NodeMinus21.w0,CompactMinus1344.checked1344,CompactMinus1344.small1344,CompactMinus1344.nodes1344,NodeMinus21.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1344.p1345,GridMinus.atNode 1345,GridMinus.atNode 1346,NodeMinus21.w1,CompactMinus1344.checked1345,CompactMinus1344.small1345,CompactMinus1344.nodes1345,NodeMinus21.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1344.p1346,GridMinus.atNode 1346,GridMinus.atNode 1347,NodeMinus21.w2,CompactMinus1344.checked1346,CompactMinus1344.small1346,CompactMinus1344.nodes1346,NodeMinus21.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1344.p1347,GridMinus.atNode 1347,GridMinus.atNode 1348,NodeMinus21.w3,CompactMinus1344.checked1347,CompactMinus1344.small1347,CompactMinus1344.nodes1347,NodeMinus21.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1344.p1348,GridMinus.atNode 1348,GridMinus.atNode 1349,NodeMinus21.w4,CompactMinus1344.checked1348,CompactMinus1344.small1348,CompactMinus1344.nodes1348,NodeMinus21.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1344.p1349,GridMinus.atNode 1349,GridMinus.atNode 1350,NodeMinus21.w5,CompactMinus1344.checked1349,CompactMinus1344.small1349,CompactMinus1344.nodes1349,NodeMinus21.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1344.p1350,GridMinus.atNode 1350,GridMinus.atNode 1351,NodeMinus21.w6,CompactMinus1344.checked1350,CompactMinus1344.small1350,CompactMinus1344.nodes1350,NodeMinus21.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1344.p1351,GridMinus.atNode 1351,GridMinus.atNode 1352,NodeMinus21.w7,CompactMinus1344.checked1351,CompactMinus1344.small1351,CompactMinus1344.nodes1351,NodeMinus21.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1344.p1352,GridMinus.atNode 1352,GridMinus.atNode 1353,NodeMinus21.w8,CompactMinus1344.checked1352,CompactMinus1344.small1352,CompactMinus1344.nodes1352,NodeMinus21.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1344.p1353,GridMinus.atNode 1353,GridMinus.atNode 1354,NodeMinus21.w9,CompactMinus1344.checked1353,CompactMinus1344.small1353,CompactMinus1344.nodes1353,NodeMinus21.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1344.p1354,GridMinus.atNode 1354,GridMinus.atNode 1355,NodeMinus21.w10,CompactMinus1344.checked1354,CompactMinus1344.small1354,CompactMinus1344.nodes1354,NodeMinus21.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1344.p1355,GridMinus.atNode 1355,GridMinus.atNode 1356,NodeMinus21.w11,CompactMinus1344.checked1355,CompactMinus1344.small1355,CompactMinus1344.nodes1355,NodeMinus21.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1344.p1356,GridMinus.atNode 1356,GridMinus.atNode 1357,NodeMinus21.w12,CompactMinus1344.checked1356,CompactMinus1344.small1356,CompactMinus1344.nodes1356,NodeMinus21.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1344.p1357,GridMinus.atNode 1357,GridMinus.atNode 1358,NodeMinus21.w13,CompactMinus1344.checked1357,CompactMinus1344.small1357,CompactMinus1344.nodes1357,NodeMinus21.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1344.p1358,GridMinus.atNode 1358,GridMinus.atNode 1359,NodeMinus21.w14,CompactMinus1344.checked1358,CompactMinus1344.small1358,CompactMinus1344.nodes1358,NodeMinus21.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1344.p1359,GridMinus.atNode 1359,GridMinus.atNode 1360,NodeMinus21.w15,CompactMinus1344.checked1359,CompactMinus1344.small1359,CompactMinus1344.nodes1359,NodeMinus21.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1360.p1360,GridMinus.atNode 1360,GridMinus.atNode 1361,NodeMinus21.w16,CompactMinus1360.checked1360,CompactMinus1360.small1360,CompactMinus1360.nodes1360,NodeMinus21.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1360.p1361,GridMinus.atNode 1361,GridMinus.atNode 1362,NodeMinus21.w17,CompactMinus1360.checked1361,CompactMinus1360.small1361,CompactMinus1360.nodes1361,NodeMinus21.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1360.p1362,GridMinus.atNode 1362,GridMinus.atNode 1363,NodeMinus21.w18,CompactMinus1360.checked1362,CompactMinus1360.small1362,CompactMinus1360.nodes1362,NodeMinus21.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1360.p1363,GridMinus.atNode 1363,GridMinus.atNode 1364,NodeMinus21.w19,CompactMinus1360.checked1363,CompactMinus1360.small1363,CompactMinus1360.nodes1363,NodeMinus21.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1360.p1364,GridMinus.atNode 1364,GridMinus.atNode 1365,NodeMinus21.w20,CompactMinus1360.checked1364,CompactMinus1360.small1364,CompactMinus1360.nodes1364,NodeMinus21.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1360.p1365,GridMinus.atNode 1365,GridMinus.atNode 1366,NodeMinus21.w21,CompactMinus1360.checked1365,CompactMinus1360.small1365,CompactMinus1360.nodes1365,NodeMinus21.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1360.p1366,GridMinus.atNode 1366,GridMinus.atNode 1367,NodeMinus21.w22,CompactMinus1360.checked1366,CompactMinus1360.small1366,CompactMinus1360.nodes1366,NodeMinus21.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1360.p1367,GridMinus.atNode 1367,GridMinus.atNode 1368,NodeMinus21.w23,CompactMinus1360.checked1367,CompactMinus1360.small1367,CompactMinus1360.nodes1367,NodeMinus21.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1360.p1368,GridMinus.atNode 1368,GridMinus.atNode 1369,NodeMinus21.w24,CompactMinus1360.checked1368,CompactMinus1360.small1368,CompactMinus1360.nodes1368,NodeMinus21.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1360.p1369,GridMinus.atNode 1369,GridMinus.atNode 1370,NodeMinus21.w25,CompactMinus1360.checked1369,CompactMinus1360.small1369,CompactMinus1360.nodes1369,NodeMinus21.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1360.p1370,GridMinus.atNode 1370,GridMinus.atNode 1371,NodeMinus21.w26,CompactMinus1360.checked1370,CompactMinus1360.small1370,CompactMinus1360.nodes1370,NodeMinus21.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1360.p1371,GridMinus.atNode 1371,GridMinus.atNode 1372,NodeMinus21.w27,CompactMinus1360.checked1371,CompactMinus1360.small1371,CompactMinus1360.nodes1371,NodeMinus21.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1360.p1372,GridMinus.atNode 1372,GridMinus.atNode 1373,NodeMinus21.w28,CompactMinus1360.checked1372,CompactMinus1360.small1372,CompactMinus1360.nodes1372,NodeMinus21.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1360.p1373,GridMinus.atNode 1373,GridMinus.atNode 1374,NodeMinus21.w29,CompactMinus1360.checked1373,CompactMinus1360.small1373,CompactMinus1360.nodes1373,NodeMinus21.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1360.p1374,GridMinus.atNode 1374,GridMinus.atNode 1375,NodeMinus21.w30,CompactMinus1360.checked1374,CompactMinus1360.small1374,CompactMinus1360.nodes1374,NodeMinus21.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1360.p1375,GridMinus.atNode 1375,GridMinus.atNode 1376,NodeMinus21.w31,CompactMinus1360.checked1375,CompactMinus1360.small1375,CompactMinus1360.nodes1375,NodeMinus21.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1376.p1376,GridMinus.atNode 1376,GridMinus.atNode 1377,NodeMinus21.w32,CompactMinus1376.checked1376,CompactMinus1376.small1376,CompactMinus1376.nodes1376,NodeMinus21.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1376.p1377,GridMinus.atNode 1377,GridMinus.atNode 1378,NodeMinus21.w33,CompactMinus1376.checked1377,CompactMinus1376.small1377,CompactMinus1376.nodes1377,NodeMinus21.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1376.p1378,GridMinus.atNode 1378,GridMinus.atNode 1379,NodeMinus21.w34,CompactMinus1376.checked1378,CompactMinus1376.small1378,CompactMinus1376.nodes1378,NodeMinus21.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1376.p1379,GridMinus.atNode 1379,GridMinus.atNode 1380,NodeMinus21.w35,CompactMinus1376.checked1379,CompactMinus1376.small1379,CompactMinus1376.nodes1379,NodeMinus21.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1376.p1380,GridMinus.atNode 1380,GridMinus.atNode 1381,NodeMinus21.w36,CompactMinus1376.checked1380,CompactMinus1376.small1380,CompactMinus1376.nodes1380,NodeMinus21.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1376.p1381,GridMinus.atNode 1381,GridMinus.atNode 1382,NodeMinus21.w37,CompactMinus1376.checked1381,CompactMinus1376.small1381,CompactMinus1376.nodes1381,NodeMinus21.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1376.p1382,GridMinus.atNode 1382,GridMinus.atNode 1383,NodeMinus21.w38,CompactMinus1376.checked1382,CompactMinus1376.small1382,CompactMinus1376.nodes1382,NodeMinus21.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1376.p1383,GridMinus.atNode 1383,GridMinus.atNode 1384,NodeMinus21.w39,CompactMinus1376.checked1383,CompactMinus1376.small1383,CompactMinus1376.nodes1383,NodeMinus21.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1376.p1384,GridMinus.atNode 1384,GridMinus.atNode 1385,NodeMinus21.w40,CompactMinus1376.checked1384,CompactMinus1376.small1384,CompactMinus1376.nodes1384,NodeMinus21.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1376.p1385,GridMinus.atNode 1385,GridMinus.atNode 1386,NodeMinus21.w41,CompactMinus1376.checked1385,CompactMinus1376.small1385,CompactMinus1376.nodes1385,NodeMinus21.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1376.p1386,GridMinus.atNode 1386,GridMinus.atNode 1387,NodeMinus21.w42,CompactMinus1376.checked1386,CompactMinus1376.small1386,CompactMinus1376.nodes1386,NodeMinus21.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1376.p1387,GridMinus.atNode 1387,GridMinus.atNode 1388,NodeMinus21.w43,CompactMinus1376.checked1387,CompactMinus1376.small1387,CompactMinus1376.nodes1387,NodeMinus21.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1376.p1388,GridMinus.atNode 1388,GridMinus.atNode 1389,NodeMinus21.w44,CompactMinus1376.checked1388,CompactMinus1376.small1388,CompactMinus1376.nodes1388,NodeMinus21.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1376.p1389,GridMinus.atNode 1389,GridMinus.atNode 1390,NodeMinus21.w45,CompactMinus1376.checked1389,CompactMinus1376.small1389,CompactMinus1376.nodes1389,NodeMinus21.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1376.p1390,GridMinus.atNode 1390,GridMinus.atNode 1391,NodeMinus21.w46,CompactMinus1376.checked1390,CompactMinus1376.small1390,CompactMinus1376.nodes1390,NodeMinus21.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1376.p1391,GridMinus.atNode 1391,GridMinus.atNode 1392,NodeMinus21.w47,CompactMinus1376.checked1391,CompactMinus1376.small1391,CompactMinus1376.nodes1391,NodeMinus21.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1392.p1392,GridMinus.atNode 1392,GridMinus.atNode 1393,NodeMinus21.w48,CompactMinus1392.checked1392,CompactMinus1392.small1392,CompactMinus1392.nodes1392,NodeMinus21.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1392.p1393,GridMinus.atNode 1393,GridMinus.atNode 1394,NodeMinus21.w49,CompactMinus1392.checked1393,CompactMinus1392.small1393,CompactMinus1392.nodes1393,NodeMinus21.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1392.p1394,GridMinus.atNode 1394,GridMinus.atNode 1395,NodeMinus21.w50,CompactMinus1392.checked1394,CompactMinus1392.small1394,CompactMinus1392.nodes1394,NodeMinus21.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1392.p1395,GridMinus.atNode 1395,GridMinus.atNode 1396,NodeMinus21.w51,CompactMinus1392.checked1395,CompactMinus1392.small1395,CompactMinus1392.nodes1395,NodeMinus21.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1392.p1396,GridMinus.atNode 1396,GridMinus.atNode 1397,NodeMinus21.w52,CompactMinus1392.checked1396,CompactMinus1392.small1396,CompactMinus1392.nodes1396,NodeMinus21.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1392.p1397,GridMinus.atNode 1397,GridMinus.atNode 1398,NodeMinus21.w53,CompactMinus1392.checked1397,CompactMinus1392.small1397,CompactMinus1392.nodes1397,NodeMinus21.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1392.p1398,GridMinus.atNode 1398,GridMinus.atNode 1399,NodeMinus21.w54,CompactMinus1392.checked1398,CompactMinus1392.small1398,CompactMinus1392.nodes1398,NodeMinus21.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1392.p1399,GridMinus.atNode 1399,GridMinus.atNode 1400,NodeMinus21.w55,CompactMinus1392.checked1399,CompactMinus1392.small1399,CompactMinus1392.nodes1399,NodeMinus21.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1392.p1400,GridMinus.atNode 1400,GridMinus.atNode 1401,NodeMinus21.w56,CompactMinus1392.checked1400,CompactMinus1392.small1400,CompactMinus1392.nodes1400,NodeMinus21.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1392.p1401,GridMinus.atNode 1401,GridMinus.atNode 1402,NodeMinus21.w57,CompactMinus1392.checked1401,CompactMinus1392.small1401,CompactMinus1392.nodes1401,NodeMinus21.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1392.p1402,GridMinus.atNode 1402,GridMinus.atNode 1403,NodeMinus21.w58,CompactMinus1392.checked1402,CompactMinus1392.small1402,CompactMinus1392.nodes1402,NodeMinus21.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1392.p1403,GridMinus.atNode 1403,GridMinus.atNode 1404,NodeMinus21.w59,CompactMinus1392.checked1403,CompactMinus1392.small1403,CompactMinus1392.nodes1403,NodeMinus21.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1392.p1404,GridMinus.atNode 1404,GridMinus.atNode 1405,NodeMinus21.w60,CompactMinus1392.checked1404,CompactMinus1392.small1404,CompactMinus1392.nodes1404,NodeMinus21.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1392.p1405,GridMinus.atNode 1405,GridMinus.atNode 1406,NodeMinus21.w61,CompactMinus1392.checked1405,CompactMinus1392.small1405,CompactMinus1392.nodes1405,NodeMinus21.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1392.p1406,GridMinus.atNode 1406,GridMinus.atNode 1407,NodeMinus21.w62,CompactMinus1392.checked1406,CompactMinus1392.small1406,CompactMinus1392.nodes1406,NodeMinus21.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1392.p1407,GridMinus.atNode 1407,GridMinus.atNode 1408,NodeMinus21.w63,CompactMinus1392.checked1407,CompactMinus1392.small1407,CompactMinus1392.nodes1407,NodeMinus21.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (1344+j) ∧
    (atRow j).right=GridMinus.atNode (1344+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus21
