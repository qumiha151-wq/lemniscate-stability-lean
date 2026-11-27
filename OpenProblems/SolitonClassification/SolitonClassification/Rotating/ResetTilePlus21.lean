import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus1344
import SolitonClassification.Rotating.ResetPackedPlus1360
import SolitonClassification.Rotating.ResetPackedPlus1376
import SolitonClassification.Rotating.ResetPackedPlus1392
namespace SolitonClassification.Rotating.DyadicReset.TilePlus21
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus1344.p1344,GridPlus.atNode 1344,GridPlus.atNode 1345,NodePlus21.w0,CompactPlus1344.checked1344,CompactPlus1344.small1344,CompactPlus1344.nodes1344,NodePlus21.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus1344.p1345,GridPlus.atNode 1345,GridPlus.atNode 1346,NodePlus21.w1,CompactPlus1344.checked1345,CompactPlus1344.small1345,CompactPlus1344.nodes1345,NodePlus21.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus1344.p1346,GridPlus.atNode 1346,GridPlus.atNode 1347,NodePlus21.w2,CompactPlus1344.checked1346,CompactPlus1344.small1346,CompactPlus1344.nodes1346,NodePlus21.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus1344.p1347,GridPlus.atNode 1347,GridPlus.atNode 1348,NodePlus21.w3,CompactPlus1344.checked1347,CompactPlus1344.small1347,CompactPlus1344.nodes1347,NodePlus21.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus1344.p1348,GridPlus.atNode 1348,GridPlus.atNode 1349,NodePlus21.w4,CompactPlus1344.checked1348,CompactPlus1344.small1348,CompactPlus1344.nodes1348,NodePlus21.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus1344.p1349,GridPlus.atNode 1349,GridPlus.atNode 1350,NodePlus21.w5,CompactPlus1344.checked1349,CompactPlus1344.small1349,CompactPlus1344.nodes1349,NodePlus21.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus1344.p1350,GridPlus.atNode 1350,GridPlus.atNode 1351,NodePlus21.w6,CompactPlus1344.checked1350,CompactPlus1344.small1350,CompactPlus1344.nodes1350,NodePlus21.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus1344.p1351,GridPlus.atNode 1351,GridPlus.atNode 1352,NodePlus21.w7,CompactPlus1344.checked1351,CompactPlus1344.small1351,CompactPlus1344.nodes1351,NodePlus21.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus1344.p1352,GridPlus.atNode 1352,GridPlus.atNode 1353,NodePlus21.w8,CompactPlus1344.checked1352,CompactPlus1344.small1352,CompactPlus1344.nodes1352,NodePlus21.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus1344.p1353,GridPlus.atNode 1353,GridPlus.atNode 1354,NodePlus21.w9,CompactPlus1344.checked1353,CompactPlus1344.small1353,CompactPlus1344.nodes1353,NodePlus21.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus1344.p1354,GridPlus.atNode 1354,GridPlus.atNode 1355,NodePlus21.w10,CompactPlus1344.checked1354,CompactPlus1344.small1354,CompactPlus1344.nodes1354,NodePlus21.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus1344.p1355,GridPlus.atNode 1355,GridPlus.atNode 1356,NodePlus21.w11,CompactPlus1344.checked1355,CompactPlus1344.small1355,CompactPlus1344.nodes1355,NodePlus21.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus1344.p1356,GridPlus.atNode 1356,GridPlus.atNode 1357,NodePlus21.w12,CompactPlus1344.checked1356,CompactPlus1344.small1356,CompactPlus1344.nodes1356,NodePlus21.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus1344.p1357,GridPlus.atNode 1357,GridPlus.atNode 1358,NodePlus21.w13,CompactPlus1344.checked1357,CompactPlus1344.small1357,CompactPlus1344.nodes1357,NodePlus21.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus1344.p1358,GridPlus.atNode 1358,GridPlus.atNode 1359,NodePlus21.w14,CompactPlus1344.checked1358,CompactPlus1344.small1358,CompactPlus1344.nodes1358,NodePlus21.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus1344.p1359,GridPlus.atNode 1359,GridPlus.atNode 1360,NodePlus21.w15,CompactPlus1344.checked1359,CompactPlus1344.small1359,CompactPlus1344.nodes1359,NodePlus21.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus1360.p1360,GridPlus.atNode 1360,GridPlus.atNode 1361,NodePlus21.w16,CompactPlus1360.checked1360,CompactPlus1360.small1360,CompactPlus1360.nodes1360,NodePlus21.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus1360.p1361,GridPlus.atNode 1361,GridPlus.atNode 1362,NodePlus21.w17,CompactPlus1360.checked1361,CompactPlus1360.small1361,CompactPlus1360.nodes1361,NodePlus21.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus1360.p1362,GridPlus.atNode 1362,GridPlus.atNode 1363,NodePlus21.w18,CompactPlus1360.checked1362,CompactPlus1360.small1362,CompactPlus1360.nodes1362,NodePlus21.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus1360.p1363,GridPlus.atNode 1363,GridPlus.atNode 1364,NodePlus21.w19,CompactPlus1360.checked1363,CompactPlus1360.small1363,CompactPlus1360.nodes1363,NodePlus21.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus1360.p1364,GridPlus.atNode 1364,GridPlus.atNode 1365,NodePlus21.w20,CompactPlus1360.checked1364,CompactPlus1360.small1364,CompactPlus1360.nodes1364,NodePlus21.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus1360.p1365,GridPlus.atNode 1365,GridPlus.atNode 1366,NodePlus21.w21,CompactPlus1360.checked1365,CompactPlus1360.small1365,CompactPlus1360.nodes1365,NodePlus21.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus1360.p1366,GridPlus.atNode 1366,GridPlus.atNode 1367,NodePlus21.w22,CompactPlus1360.checked1366,CompactPlus1360.small1366,CompactPlus1360.nodes1366,NodePlus21.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus1360.p1367,GridPlus.atNode 1367,GridPlus.atNode 1368,NodePlus21.w23,CompactPlus1360.checked1367,CompactPlus1360.small1367,CompactPlus1360.nodes1367,NodePlus21.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus1360.p1368,GridPlus.atNode 1368,GridPlus.atNode 1369,NodePlus21.w24,CompactPlus1360.checked1368,CompactPlus1360.small1368,CompactPlus1360.nodes1368,NodePlus21.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus1360.p1369,GridPlus.atNode 1369,GridPlus.atNode 1370,NodePlus21.w25,CompactPlus1360.checked1369,CompactPlus1360.small1369,CompactPlus1360.nodes1369,NodePlus21.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus1360.p1370,GridPlus.atNode 1370,GridPlus.atNode 1371,NodePlus21.w26,CompactPlus1360.checked1370,CompactPlus1360.small1370,CompactPlus1360.nodes1370,NodePlus21.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus1360.p1371,GridPlus.atNode 1371,GridPlus.atNode 1372,NodePlus21.w27,CompactPlus1360.checked1371,CompactPlus1360.small1371,CompactPlus1360.nodes1371,NodePlus21.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus1360.p1372,GridPlus.atNode 1372,GridPlus.atNode 1373,NodePlus21.w28,CompactPlus1360.checked1372,CompactPlus1360.small1372,CompactPlus1360.nodes1372,NodePlus21.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus1360.p1373,GridPlus.atNode 1373,GridPlus.atNode 1374,NodePlus21.w29,CompactPlus1360.checked1373,CompactPlus1360.small1373,CompactPlus1360.nodes1373,NodePlus21.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus1360.p1374,GridPlus.atNode 1374,GridPlus.atNode 1375,NodePlus21.w30,CompactPlus1360.checked1374,CompactPlus1360.small1374,CompactPlus1360.nodes1374,NodePlus21.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus1360.p1375,GridPlus.atNode 1375,GridPlus.atNode 1376,NodePlus21.w31,CompactPlus1360.checked1375,CompactPlus1360.small1375,CompactPlus1360.nodes1375,NodePlus21.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus1376.p1376,GridPlus.atNode 1376,GridPlus.atNode 1377,NodePlus21.w32,CompactPlus1376.checked1376,CompactPlus1376.small1376,CompactPlus1376.nodes1376,NodePlus21.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus1376.p1377,GridPlus.atNode 1377,GridPlus.atNode 1378,NodePlus21.w33,CompactPlus1376.checked1377,CompactPlus1376.small1377,CompactPlus1376.nodes1377,NodePlus21.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus1376.p1378,GridPlus.atNode 1378,GridPlus.atNode 1379,NodePlus21.w34,CompactPlus1376.checked1378,CompactPlus1376.small1378,CompactPlus1376.nodes1378,NodePlus21.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus1376.p1379,GridPlus.atNode 1379,GridPlus.atNode 1380,NodePlus21.w35,CompactPlus1376.checked1379,CompactPlus1376.small1379,CompactPlus1376.nodes1379,NodePlus21.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus1376.p1380,GridPlus.atNode 1380,GridPlus.atNode 1381,NodePlus21.w36,CompactPlus1376.checked1380,CompactPlus1376.small1380,CompactPlus1376.nodes1380,NodePlus21.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus1376.p1381,GridPlus.atNode 1381,GridPlus.atNode 1382,NodePlus21.w37,CompactPlus1376.checked1381,CompactPlus1376.small1381,CompactPlus1376.nodes1381,NodePlus21.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus1376.p1382,GridPlus.atNode 1382,GridPlus.atNode 1383,NodePlus21.w38,CompactPlus1376.checked1382,CompactPlus1376.small1382,CompactPlus1376.nodes1382,NodePlus21.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus1376.p1383,GridPlus.atNode 1383,GridPlus.atNode 1384,NodePlus21.w39,CompactPlus1376.checked1383,CompactPlus1376.small1383,CompactPlus1376.nodes1383,NodePlus21.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus1376.p1384,GridPlus.atNode 1384,GridPlus.atNode 1385,NodePlus21.w40,CompactPlus1376.checked1384,CompactPlus1376.small1384,CompactPlus1376.nodes1384,NodePlus21.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus1376.p1385,GridPlus.atNode 1385,GridPlus.atNode 1386,NodePlus21.w41,CompactPlus1376.checked1385,CompactPlus1376.small1385,CompactPlus1376.nodes1385,NodePlus21.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus1376.p1386,GridPlus.atNode 1386,GridPlus.atNode 1387,NodePlus21.w42,CompactPlus1376.checked1386,CompactPlus1376.small1386,CompactPlus1376.nodes1386,NodePlus21.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus1376.p1387,GridPlus.atNode 1387,GridPlus.atNode 1388,NodePlus21.w43,CompactPlus1376.checked1387,CompactPlus1376.small1387,CompactPlus1376.nodes1387,NodePlus21.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus1376.p1388,GridPlus.atNode 1388,GridPlus.atNode 1389,NodePlus21.w44,CompactPlus1376.checked1388,CompactPlus1376.small1388,CompactPlus1376.nodes1388,NodePlus21.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus1376.p1389,GridPlus.atNode 1389,GridPlus.atNode 1390,NodePlus21.w45,CompactPlus1376.checked1389,CompactPlus1376.small1389,CompactPlus1376.nodes1389,NodePlus21.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus1376.p1390,GridPlus.atNode 1390,GridPlus.atNode 1391,NodePlus21.w46,CompactPlus1376.checked1390,CompactPlus1376.small1390,CompactPlus1376.nodes1390,NodePlus21.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus1376.p1391,GridPlus.atNode 1391,GridPlus.atNode 1392,NodePlus21.w47,CompactPlus1376.checked1391,CompactPlus1376.small1391,CompactPlus1376.nodes1391,NodePlus21.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus1392.p1392,GridPlus.atNode 1392,GridPlus.atNode 1393,NodePlus21.w48,CompactPlus1392.checked1392,CompactPlus1392.small1392,CompactPlus1392.nodes1392,NodePlus21.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus1392.p1393,GridPlus.atNode 1393,GridPlus.atNode 1394,NodePlus21.w49,CompactPlus1392.checked1393,CompactPlus1392.small1393,CompactPlus1392.nodes1393,NodePlus21.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus1392.p1394,GridPlus.atNode 1394,GridPlus.atNode 1395,NodePlus21.w50,CompactPlus1392.checked1394,CompactPlus1392.small1394,CompactPlus1392.nodes1394,NodePlus21.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus1392.p1395,GridPlus.atNode 1395,GridPlus.atNode 1396,NodePlus21.w51,CompactPlus1392.checked1395,CompactPlus1392.small1395,CompactPlus1392.nodes1395,NodePlus21.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus1392.p1396,GridPlus.atNode 1396,GridPlus.atNode 1397,NodePlus21.w52,CompactPlus1392.checked1396,CompactPlus1392.small1396,CompactPlus1392.nodes1396,NodePlus21.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus1392.p1397,GridPlus.atNode 1397,GridPlus.atNode 1398,NodePlus21.w53,CompactPlus1392.checked1397,CompactPlus1392.small1397,CompactPlus1392.nodes1397,NodePlus21.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus1392.p1398,GridPlus.atNode 1398,GridPlus.atNode 1399,NodePlus21.w54,CompactPlus1392.checked1398,CompactPlus1392.small1398,CompactPlus1392.nodes1398,NodePlus21.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus1392.p1399,GridPlus.atNode 1399,GridPlus.atNode 1400,NodePlus21.w55,CompactPlus1392.checked1399,CompactPlus1392.small1399,CompactPlus1392.nodes1399,NodePlus21.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus1392.p1400,GridPlus.atNode 1400,GridPlus.atNode 1401,NodePlus21.w56,CompactPlus1392.checked1400,CompactPlus1392.small1400,CompactPlus1392.nodes1400,NodePlus21.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus1392.p1401,GridPlus.atNode 1401,GridPlus.atNode 1402,NodePlus21.w57,CompactPlus1392.checked1401,CompactPlus1392.small1401,CompactPlus1392.nodes1401,NodePlus21.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus1392.p1402,GridPlus.atNode 1402,GridPlus.atNode 1403,NodePlus21.w58,CompactPlus1392.checked1402,CompactPlus1392.small1402,CompactPlus1392.nodes1402,NodePlus21.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus1392.p1403,GridPlus.atNode 1403,GridPlus.atNode 1404,NodePlus21.w59,CompactPlus1392.checked1403,CompactPlus1392.small1403,CompactPlus1392.nodes1403,NodePlus21.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus1392.p1404,GridPlus.atNode 1404,GridPlus.atNode 1405,NodePlus21.w60,CompactPlus1392.checked1404,CompactPlus1392.small1404,CompactPlus1392.nodes1404,NodePlus21.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus1392.p1405,GridPlus.atNode 1405,GridPlus.atNode 1406,NodePlus21.w61,CompactPlus1392.checked1405,CompactPlus1392.small1405,CompactPlus1392.nodes1405,NodePlus21.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus1392.p1406,GridPlus.atNode 1406,GridPlus.atNode 1407,NodePlus21.w62,CompactPlus1392.checked1406,CompactPlus1392.small1406,CompactPlus1392.nodes1406,NodePlus21.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus1392.p1407,GridPlus.atNode 1407,GridPlus.atNode 1408,NodePlus21.w63,CompactPlus1392.checked1407,CompactPlus1392.small1407,CompactPlus1392.nodes1407,NodePlus21.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (1344+j) ∧
    (atRow j).right=GridPlus.atNode (1344+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus21
