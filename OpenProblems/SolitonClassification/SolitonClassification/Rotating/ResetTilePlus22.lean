import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus1408
import SolitonClassification.Rotating.ResetPackedPlus1424
import SolitonClassification.Rotating.ResetPackedPlus1440
import SolitonClassification.Rotating.ResetPackedPlus1456
namespace SolitonClassification.Rotating.DyadicReset.TilePlus22
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus1408.p1408,GridPlus.atNode 1408,GridPlus.atNode 1409,NodePlus22.w0,CompactPlus1408.checked1408,CompactPlus1408.small1408,CompactPlus1408.nodes1408,NodePlus22.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus1408.p1409,GridPlus.atNode 1409,GridPlus.atNode 1410,NodePlus22.w1,CompactPlus1408.checked1409,CompactPlus1408.small1409,CompactPlus1408.nodes1409,NodePlus22.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus1408.p1410,GridPlus.atNode 1410,GridPlus.atNode 1411,NodePlus22.w2,CompactPlus1408.checked1410,CompactPlus1408.small1410,CompactPlus1408.nodes1410,NodePlus22.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus1408.p1411,GridPlus.atNode 1411,GridPlus.atNode 1412,NodePlus22.w3,CompactPlus1408.checked1411,CompactPlus1408.small1411,CompactPlus1408.nodes1411,NodePlus22.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus1408.p1412,GridPlus.atNode 1412,GridPlus.atNode 1413,NodePlus22.w4,CompactPlus1408.checked1412,CompactPlus1408.small1412,CompactPlus1408.nodes1412,NodePlus22.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus1408.p1413,GridPlus.atNode 1413,GridPlus.atNode 1414,NodePlus22.w5,CompactPlus1408.checked1413,CompactPlus1408.small1413,CompactPlus1408.nodes1413,NodePlus22.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus1408.p1414,GridPlus.atNode 1414,GridPlus.atNode 1415,NodePlus22.w6,CompactPlus1408.checked1414,CompactPlus1408.small1414,CompactPlus1408.nodes1414,NodePlus22.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus1408.p1415,GridPlus.atNode 1415,GridPlus.atNode 1416,NodePlus22.w7,CompactPlus1408.checked1415,CompactPlus1408.small1415,CompactPlus1408.nodes1415,NodePlus22.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus1408.p1416,GridPlus.atNode 1416,GridPlus.atNode 1417,NodePlus22.w8,CompactPlus1408.checked1416,CompactPlus1408.small1416,CompactPlus1408.nodes1416,NodePlus22.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus1408.p1417,GridPlus.atNode 1417,GridPlus.atNode 1418,NodePlus22.w9,CompactPlus1408.checked1417,CompactPlus1408.small1417,CompactPlus1408.nodes1417,NodePlus22.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus1408.p1418,GridPlus.atNode 1418,GridPlus.atNode 1419,NodePlus22.w10,CompactPlus1408.checked1418,CompactPlus1408.small1418,CompactPlus1408.nodes1418,NodePlus22.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus1408.p1419,GridPlus.atNode 1419,GridPlus.atNode 1420,NodePlus22.w11,CompactPlus1408.checked1419,CompactPlus1408.small1419,CompactPlus1408.nodes1419,NodePlus22.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus1408.p1420,GridPlus.atNode 1420,GridPlus.atNode 1421,NodePlus22.w12,CompactPlus1408.checked1420,CompactPlus1408.small1420,CompactPlus1408.nodes1420,NodePlus22.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus1408.p1421,GridPlus.atNode 1421,GridPlus.atNode 1422,NodePlus22.w13,CompactPlus1408.checked1421,CompactPlus1408.small1421,CompactPlus1408.nodes1421,NodePlus22.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus1408.p1422,GridPlus.atNode 1422,GridPlus.atNode 1423,NodePlus22.w14,CompactPlus1408.checked1422,CompactPlus1408.small1422,CompactPlus1408.nodes1422,NodePlus22.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus1408.p1423,GridPlus.atNode 1423,GridPlus.atNode 1424,NodePlus22.w15,CompactPlus1408.checked1423,CompactPlus1408.small1423,CompactPlus1408.nodes1423,NodePlus22.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus1424.p1424,GridPlus.atNode 1424,GridPlus.atNode 1425,NodePlus22.w16,CompactPlus1424.checked1424,CompactPlus1424.small1424,CompactPlus1424.nodes1424,NodePlus22.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus1424.p1425,GridPlus.atNode 1425,GridPlus.atNode 1426,NodePlus22.w17,CompactPlus1424.checked1425,CompactPlus1424.small1425,CompactPlus1424.nodes1425,NodePlus22.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus1424.p1426,GridPlus.atNode 1426,GridPlus.atNode 1427,NodePlus22.w18,CompactPlus1424.checked1426,CompactPlus1424.small1426,CompactPlus1424.nodes1426,NodePlus22.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus1424.p1427,GridPlus.atNode 1427,GridPlus.atNode 1428,NodePlus22.w19,CompactPlus1424.checked1427,CompactPlus1424.small1427,CompactPlus1424.nodes1427,NodePlus22.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus1424.p1428,GridPlus.atNode 1428,GridPlus.atNode 1429,NodePlus22.w20,CompactPlus1424.checked1428,CompactPlus1424.small1428,CompactPlus1424.nodes1428,NodePlus22.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus1424.p1429,GridPlus.atNode 1429,GridPlus.atNode 1430,NodePlus22.w21,CompactPlus1424.checked1429,CompactPlus1424.small1429,CompactPlus1424.nodes1429,NodePlus22.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus1424.p1430,GridPlus.atNode 1430,GridPlus.atNode 1431,NodePlus22.w22,CompactPlus1424.checked1430,CompactPlus1424.small1430,CompactPlus1424.nodes1430,NodePlus22.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus1424.p1431,GridPlus.atNode 1431,GridPlus.atNode 1432,NodePlus22.w23,CompactPlus1424.checked1431,CompactPlus1424.small1431,CompactPlus1424.nodes1431,NodePlus22.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus1424.p1432,GridPlus.atNode 1432,GridPlus.atNode 1433,NodePlus22.w24,CompactPlus1424.checked1432,CompactPlus1424.small1432,CompactPlus1424.nodes1432,NodePlus22.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus1424.p1433,GridPlus.atNode 1433,GridPlus.atNode 1434,NodePlus22.w25,CompactPlus1424.checked1433,CompactPlus1424.small1433,CompactPlus1424.nodes1433,NodePlus22.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus1424.p1434,GridPlus.atNode 1434,GridPlus.atNode 1435,NodePlus22.w26,CompactPlus1424.checked1434,CompactPlus1424.small1434,CompactPlus1424.nodes1434,NodePlus22.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus1424.p1435,GridPlus.atNode 1435,GridPlus.atNode 1436,NodePlus22.w27,CompactPlus1424.checked1435,CompactPlus1424.small1435,CompactPlus1424.nodes1435,NodePlus22.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus1424.p1436,GridPlus.atNode 1436,GridPlus.atNode 1437,NodePlus22.w28,CompactPlus1424.checked1436,CompactPlus1424.small1436,CompactPlus1424.nodes1436,NodePlus22.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus1424.p1437,GridPlus.atNode 1437,GridPlus.atNode 1438,NodePlus22.w29,CompactPlus1424.checked1437,CompactPlus1424.small1437,CompactPlus1424.nodes1437,NodePlus22.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus1424.p1438,GridPlus.atNode 1438,GridPlus.atNode 1439,NodePlus22.w30,CompactPlus1424.checked1438,CompactPlus1424.small1438,CompactPlus1424.nodes1438,NodePlus22.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus1424.p1439,GridPlus.atNode 1439,GridPlus.atNode 1440,NodePlus22.w31,CompactPlus1424.checked1439,CompactPlus1424.small1439,CompactPlus1424.nodes1439,NodePlus22.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus1440.p1440,GridPlus.atNode 1440,GridPlus.atNode 1441,NodePlus22.w32,CompactPlus1440.checked1440,CompactPlus1440.small1440,CompactPlus1440.nodes1440,NodePlus22.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus1440.p1441,GridPlus.atNode 1441,GridPlus.atNode 1442,NodePlus22.w33,CompactPlus1440.checked1441,CompactPlus1440.small1441,CompactPlus1440.nodes1441,NodePlus22.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus1440.p1442,GridPlus.atNode 1442,GridPlus.atNode 1443,NodePlus22.w34,CompactPlus1440.checked1442,CompactPlus1440.small1442,CompactPlus1440.nodes1442,NodePlus22.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus1440.p1443,GridPlus.atNode 1443,GridPlus.atNode 1444,NodePlus22.w35,CompactPlus1440.checked1443,CompactPlus1440.small1443,CompactPlus1440.nodes1443,NodePlus22.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus1440.p1444,GridPlus.atNode 1444,GridPlus.atNode 1445,NodePlus22.w36,CompactPlus1440.checked1444,CompactPlus1440.small1444,CompactPlus1440.nodes1444,NodePlus22.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus1440.p1445,GridPlus.atNode 1445,GridPlus.atNode 1446,NodePlus22.w37,CompactPlus1440.checked1445,CompactPlus1440.small1445,CompactPlus1440.nodes1445,NodePlus22.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus1440.p1446,GridPlus.atNode 1446,GridPlus.atNode 1447,NodePlus22.w38,CompactPlus1440.checked1446,CompactPlus1440.small1446,CompactPlus1440.nodes1446,NodePlus22.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus1440.p1447,GridPlus.atNode 1447,GridPlus.atNode 1448,NodePlus22.w39,CompactPlus1440.checked1447,CompactPlus1440.small1447,CompactPlus1440.nodes1447,NodePlus22.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus1440.p1448,GridPlus.atNode 1448,GridPlus.atNode 1449,NodePlus22.w40,CompactPlus1440.checked1448,CompactPlus1440.small1448,CompactPlus1440.nodes1448,NodePlus22.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus1440.p1449,GridPlus.atNode 1449,GridPlus.atNode 1450,NodePlus22.w41,CompactPlus1440.checked1449,CompactPlus1440.small1449,CompactPlus1440.nodes1449,NodePlus22.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus1440.p1450,GridPlus.atNode 1450,GridPlus.atNode 1451,NodePlus22.w42,CompactPlus1440.checked1450,CompactPlus1440.small1450,CompactPlus1440.nodes1450,NodePlus22.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus1440.p1451,GridPlus.atNode 1451,GridPlus.atNode 1452,NodePlus22.w43,CompactPlus1440.checked1451,CompactPlus1440.small1451,CompactPlus1440.nodes1451,NodePlus22.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus1440.p1452,GridPlus.atNode 1452,GridPlus.atNode 1453,NodePlus22.w44,CompactPlus1440.checked1452,CompactPlus1440.small1452,CompactPlus1440.nodes1452,NodePlus22.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus1440.p1453,GridPlus.atNode 1453,GridPlus.atNode 1454,NodePlus22.w45,CompactPlus1440.checked1453,CompactPlus1440.small1453,CompactPlus1440.nodes1453,NodePlus22.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus1440.p1454,GridPlus.atNode 1454,GridPlus.atNode 1455,NodePlus22.w46,CompactPlus1440.checked1454,CompactPlus1440.small1454,CompactPlus1440.nodes1454,NodePlus22.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus1440.p1455,GridPlus.atNode 1455,GridPlus.atNode 1456,NodePlus22.w47,CompactPlus1440.checked1455,CompactPlus1440.small1455,CompactPlus1440.nodes1455,NodePlus22.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus1456.p1456,GridPlus.atNode 1456,GridPlus.atNode 1457,NodePlus22.w48,CompactPlus1456.checked1456,CompactPlus1456.small1456,CompactPlus1456.nodes1456,NodePlus22.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus1456.p1457,GridPlus.atNode 1457,GridPlus.atNode 1458,NodePlus22.w49,CompactPlus1456.checked1457,CompactPlus1456.small1457,CompactPlus1456.nodes1457,NodePlus22.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus1456.p1458,GridPlus.atNode 1458,GridPlus.atNode 1459,NodePlus22.w50,CompactPlus1456.checked1458,CompactPlus1456.small1458,CompactPlus1456.nodes1458,NodePlus22.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus1456.p1459,GridPlus.atNode 1459,GridPlus.atNode 1460,NodePlus22.w51,CompactPlus1456.checked1459,CompactPlus1456.small1459,CompactPlus1456.nodes1459,NodePlus22.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus1456.p1460,GridPlus.atNode 1460,GridPlus.atNode 1461,NodePlus22.w52,CompactPlus1456.checked1460,CompactPlus1456.small1460,CompactPlus1456.nodes1460,NodePlus22.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus1456.p1461,GridPlus.atNode 1461,GridPlus.atNode 1462,NodePlus22.w53,CompactPlus1456.checked1461,CompactPlus1456.small1461,CompactPlus1456.nodes1461,NodePlus22.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus1456.p1462,GridPlus.atNode 1462,GridPlus.atNode 1463,NodePlus22.w54,CompactPlus1456.checked1462,CompactPlus1456.small1462,CompactPlus1456.nodes1462,NodePlus22.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus1456.p1463,GridPlus.atNode 1463,GridPlus.atNode 1464,NodePlus22.w55,CompactPlus1456.checked1463,CompactPlus1456.small1463,CompactPlus1456.nodes1463,NodePlus22.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus1456.p1464,GridPlus.atNode 1464,GridPlus.atNode 1465,NodePlus22.w56,CompactPlus1456.checked1464,CompactPlus1456.small1464,CompactPlus1456.nodes1464,NodePlus22.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus1456.p1465,GridPlus.atNode 1465,GridPlus.atNode 1466,NodePlus22.w57,CompactPlus1456.checked1465,CompactPlus1456.small1465,CompactPlus1456.nodes1465,NodePlus22.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus1456.p1466,GridPlus.atNode 1466,GridPlus.atNode 1467,NodePlus22.w58,CompactPlus1456.checked1466,CompactPlus1456.small1466,CompactPlus1456.nodes1466,NodePlus22.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus1456.p1467,GridPlus.atNode 1467,GridPlus.atNode 1468,NodePlus22.w59,CompactPlus1456.checked1467,CompactPlus1456.small1467,CompactPlus1456.nodes1467,NodePlus22.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus1456.p1468,GridPlus.atNode 1468,GridPlus.atNode 1469,NodePlus22.w60,CompactPlus1456.checked1468,CompactPlus1456.small1468,CompactPlus1456.nodes1468,NodePlus22.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus1456.p1469,GridPlus.atNode 1469,GridPlus.atNode 1470,NodePlus22.w61,CompactPlus1456.checked1469,CompactPlus1456.small1469,CompactPlus1456.nodes1469,NodePlus22.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus1456.p1470,GridPlus.atNode 1470,GridPlus.atNode 1471,NodePlus22.w62,CompactPlus1456.checked1470,CompactPlus1456.small1470,CompactPlus1456.nodes1470,NodePlus22.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus1456.p1471,GridPlus.atNode 1471,GridPlus.atNode 1472,NodePlus22.w63,CompactPlus1456.checked1471,CompactPlus1456.small1471,CompactPlus1456.nodes1471,NodePlus22.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (1408+j) ∧
    (atRow j).right=GridPlus.atNode (1408+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus22
