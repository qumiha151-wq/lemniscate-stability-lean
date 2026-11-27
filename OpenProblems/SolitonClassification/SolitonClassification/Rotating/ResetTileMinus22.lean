import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus1408
import SolitonClassification.Rotating.ResetPackedMinus1424
import SolitonClassification.Rotating.ResetPackedMinus1440
import SolitonClassification.Rotating.ResetPackedMinus1456
namespace SolitonClassification.Rotating.DyadicReset.TileMinus22
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1408.p1408,GridMinus.atNode 1408,GridMinus.atNode 1409,NodeMinus22.w0,CompactMinus1408.checked1408,CompactMinus1408.small1408,CompactMinus1408.nodes1408,NodeMinus22.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1408.p1409,GridMinus.atNode 1409,GridMinus.atNode 1410,NodeMinus22.w1,CompactMinus1408.checked1409,CompactMinus1408.small1409,CompactMinus1408.nodes1409,NodeMinus22.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1408.p1410,GridMinus.atNode 1410,GridMinus.atNode 1411,NodeMinus22.w2,CompactMinus1408.checked1410,CompactMinus1408.small1410,CompactMinus1408.nodes1410,NodeMinus22.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1408.p1411,GridMinus.atNode 1411,GridMinus.atNode 1412,NodeMinus22.w3,CompactMinus1408.checked1411,CompactMinus1408.small1411,CompactMinus1408.nodes1411,NodeMinus22.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1408.p1412,GridMinus.atNode 1412,GridMinus.atNode 1413,NodeMinus22.w4,CompactMinus1408.checked1412,CompactMinus1408.small1412,CompactMinus1408.nodes1412,NodeMinus22.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1408.p1413,GridMinus.atNode 1413,GridMinus.atNode 1414,NodeMinus22.w5,CompactMinus1408.checked1413,CompactMinus1408.small1413,CompactMinus1408.nodes1413,NodeMinus22.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1408.p1414,GridMinus.atNode 1414,GridMinus.atNode 1415,NodeMinus22.w6,CompactMinus1408.checked1414,CompactMinus1408.small1414,CompactMinus1408.nodes1414,NodeMinus22.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1408.p1415,GridMinus.atNode 1415,GridMinus.atNode 1416,NodeMinus22.w7,CompactMinus1408.checked1415,CompactMinus1408.small1415,CompactMinus1408.nodes1415,NodeMinus22.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1408.p1416,GridMinus.atNode 1416,GridMinus.atNode 1417,NodeMinus22.w8,CompactMinus1408.checked1416,CompactMinus1408.small1416,CompactMinus1408.nodes1416,NodeMinus22.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1408.p1417,GridMinus.atNode 1417,GridMinus.atNode 1418,NodeMinus22.w9,CompactMinus1408.checked1417,CompactMinus1408.small1417,CompactMinus1408.nodes1417,NodeMinus22.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1408.p1418,GridMinus.atNode 1418,GridMinus.atNode 1419,NodeMinus22.w10,CompactMinus1408.checked1418,CompactMinus1408.small1418,CompactMinus1408.nodes1418,NodeMinus22.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1408.p1419,GridMinus.atNode 1419,GridMinus.atNode 1420,NodeMinus22.w11,CompactMinus1408.checked1419,CompactMinus1408.small1419,CompactMinus1408.nodes1419,NodeMinus22.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1408.p1420,GridMinus.atNode 1420,GridMinus.atNode 1421,NodeMinus22.w12,CompactMinus1408.checked1420,CompactMinus1408.small1420,CompactMinus1408.nodes1420,NodeMinus22.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1408.p1421,GridMinus.atNode 1421,GridMinus.atNode 1422,NodeMinus22.w13,CompactMinus1408.checked1421,CompactMinus1408.small1421,CompactMinus1408.nodes1421,NodeMinus22.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1408.p1422,GridMinus.atNode 1422,GridMinus.atNode 1423,NodeMinus22.w14,CompactMinus1408.checked1422,CompactMinus1408.small1422,CompactMinus1408.nodes1422,NodeMinus22.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1408.p1423,GridMinus.atNode 1423,GridMinus.atNode 1424,NodeMinus22.w15,CompactMinus1408.checked1423,CompactMinus1408.small1423,CompactMinus1408.nodes1423,NodeMinus22.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1424.p1424,GridMinus.atNode 1424,GridMinus.atNode 1425,NodeMinus22.w16,CompactMinus1424.checked1424,CompactMinus1424.small1424,CompactMinus1424.nodes1424,NodeMinus22.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1424.p1425,GridMinus.atNode 1425,GridMinus.atNode 1426,NodeMinus22.w17,CompactMinus1424.checked1425,CompactMinus1424.small1425,CompactMinus1424.nodes1425,NodeMinus22.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1424.p1426,GridMinus.atNode 1426,GridMinus.atNode 1427,NodeMinus22.w18,CompactMinus1424.checked1426,CompactMinus1424.small1426,CompactMinus1424.nodes1426,NodeMinus22.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1424.p1427,GridMinus.atNode 1427,GridMinus.atNode 1428,NodeMinus22.w19,CompactMinus1424.checked1427,CompactMinus1424.small1427,CompactMinus1424.nodes1427,NodeMinus22.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1424.p1428,GridMinus.atNode 1428,GridMinus.atNode 1429,NodeMinus22.w20,CompactMinus1424.checked1428,CompactMinus1424.small1428,CompactMinus1424.nodes1428,NodeMinus22.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1424.p1429,GridMinus.atNode 1429,GridMinus.atNode 1430,NodeMinus22.w21,CompactMinus1424.checked1429,CompactMinus1424.small1429,CompactMinus1424.nodes1429,NodeMinus22.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1424.p1430,GridMinus.atNode 1430,GridMinus.atNode 1431,NodeMinus22.w22,CompactMinus1424.checked1430,CompactMinus1424.small1430,CompactMinus1424.nodes1430,NodeMinus22.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1424.p1431,GridMinus.atNode 1431,GridMinus.atNode 1432,NodeMinus22.w23,CompactMinus1424.checked1431,CompactMinus1424.small1431,CompactMinus1424.nodes1431,NodeMinus22.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1424.p1432,GridMinus.atNode 1432,GridMinus.atNode 1433,NodeMinus22.w24,CompactMinus1424.checked1432,CompactMinus1424.small1432,CompactMinus1424.nodes1432,NodeMinus22.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1424.p1433,GridMinus.atNode 1433,GridMinus.atNode 1434,NodeMinus22.w25,CompactMinus1424.checked1433,CompactMinus1424.small1433,CompactMinus1424.nodes1433,NodeMinus22.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1424.p1434,GridMinus.atNode 1434,GridMinus.atNode 1435,NodeMinus22.w26,CompactMinus1424.checked1434,CompactMinus1424.small1434,CompactMinus1424.nodes1434,NodeMinus22.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1424.p1435,GridMinus.atNode 1435,GridMinus.atNode 1436,NodeMinus22.w27,CompactMinus1424.checked1435,CompactMinus1424.small1435,CompactMinus1424.nodes1435,NodeMinus22.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1424.p1436,GridMinus.atNode 1436,GridMinus.atNode 1437,NodeMinus22.w28,CompactMinus1424.checked1436,CompactMinus1424.small1436,CompactMinus1424.nodes1436,NodeMinus22.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1424.p1437,GridMinus.atNode 1437,GridMinus.atNode 1438,NodeMinus22.w29,CompactMinus1424.checked1437,CompactMinus1424.small1437,CompactMinus1424.nodes1437,NodeMinus22.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1424.p1438,GridMinus.atNode 1438,GridMinus.atNode 1439,NodeMinus22.w30,CompactMinus1424.checked1438,CompactMinus1424.small1438,CompactMinus1424.nodes1438,NodeMinus22.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1424.p1439,GridMinus.atNode 1439,GridMinus.atNode 1440,NodeMinus22.w31,CompactMinus1424.checked1439,CompactMinus1424.small1439,CompactMinus1424.nodes1439,NodeMinus22.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1440.p1440,GridMinus.atNode 1440,GridMinus.atNode 1441,NodeMinus22.w32,CompactMinus1440.checked1440,CompactMinus1440.small1440,CompactMinus1440.nodes1440,NodeMinus22.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1440.p1441,GridMinus.atNode 1441,GridMinus.atNode 1442,NodeMinus22.w33,CompactMinus1440.checked1441,CompactMinus1440.small1441,CompactMinus1440.nodes1441,NodeMinus22.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1440.p1442,GridMinus.atNode 1442,GridMinus.atNode 1443,NodeMinus22.w34,CompactMinus1440.checked1442,CompactMinus1440.small1442,CompactMinus1440.nodes1442,NodeMinus22.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1440.p1443,GridMinus.atNode 1443,GridMinus.atNode 1444,NodeMinus22.w35,CompactMinus1440.checked1443,CompactMinus1440.small1443,CompactMinus1440.nodes1443,NodeMinus22.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1440.p1444,GridMinus.atNode 1444,GridMinus.atNode 1445,NodeMinus22.w36,CompactMinus1440.checked1444,CompactMinus1440.small1444,CompactMinus1440.nodes1444,NodeMinus22.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1440.p1445,GridMinus.atNode 1445,GridMinus.atNode 1446,NodeMinus22.w37,CompactMinus1440.checked1445,CompactMinus1440.small1445,CompactMinus1440.nodes1445,NodeMinus22.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1440.p1446,GridMinus.atNode 1446,GridMinus.atNode 1447,NodeMinus22.w38,CompactMinus1440.checked1446,CompactMinus1440.small1446,CompactMinus1440.nodes1446,NodeMinus22.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1440.p1447,GridMinus.atNode 1447,GridMinus.atNode 1448,NodeMinus22.w39,CompactMinus1440.checked1447,CompactMinus1440.small1447,CompactMinus1440.nodes1447,NodeMinus22.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1440.p1448,GridMinus.atNode 1448,GridMinus.atNode 1449,NodeMinus22.w40,CompactMinus1440.checked1448,CompactMinus1440.small1448,CompactMinus1440.nodes1448,NodeMinus22.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1440.p1449,GridMinus.atNode 1449,GridMinus.atNode 1450,NodeMinus22.w41,CompactMinus1440.checked1449,CompactMinus1440.small1449,CompactMinus1440.nodes1449,NodeMinus22.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1440.p1450,GridMinus.atNode 1450,GridMinus.atNode 1451,NodeMinus22.w42,CompactMinus1440.checked1450,CompactMinus1440.small1450,CompactMinus1440.nodes1450,NodeMinus22.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1440.p1451,GridMinus.atNode 1451,GridMinus.atNode 1452,NodeMinus22.w43,CompactMinus1440.checked1451,CompactMinus1440.small1451,CompactMinus1440.nodes1451,NodeMinus22.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1440.p1452,GridMinus.atNode 1452,GridMinus.atNode 1453,NodeMinus22.w44,CompactMinus1440.checked1452,CompactMinus1440.small1452,CompactMinus1440.nodes1452,NodeMinus22.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1440.p1453,GridMinus.atNode 1453,GridMinus.atNode 1454,NodeMinus22.w45,CompactMinus1440.checked1453,CompactMinus1440.small1453,CompactMinus1440.nodes1453,NodeMinus22.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1440.p1454,GridMinus.atNode 1454,GridMinus.atNode 1455,NodeMinus22.w46,CompactMinus1440.checked1454,CompactMinus1440.small1454,CompactMinus1440.nodes1454,NodeMinus22.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1440.p1455,GridMinus.atNode 1455,GridMinus.atNode 1456,NodeMinus22.w47,CompactMinus1440.checked1455,CompactMinus1440.small1455,CompactMinus1440.nodes1455,NodeMinus22.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1456.p1456,GridMinus.atNode 1456,GridMinus.atNode 1457,NodeMinus22.w48,CompactMinus1456.checked1456,CompactMinus1456.small1456,CompactMinus1456.nodes1456,NodeMinus22.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1456.p1457,GridMinus.atNode 1457,GridMinus.atNode 1458,NodeMinus22.w49,CompactMinus1456.checked1457,CompactMinus1456.small1457,CompactMinus1456.nodes1457,NodeMinus22.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1456.p1458,GridMinus.atNode 1458,GridMinus.atNode 1459,NodeMinus22.w50,CompactMinus1456.checked1458,CompactMinus1456.small1458,CompactMinus1456.nodes1458,NodeMinus22.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1456.p1459,GridMinus.atNode 1459,GridMinus.atNode 1460,NodeMinus22.w51,CompactMinus1456.checked1459,CompactMinus1456.small1459,CompactMinus1456.nodes1459,NodeMinus22.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1456.p1460,GridMinus.atNode 1460,GridMinus.atNode 1461,NodeMinus22.w52,CompactMinus1456.checked1460,CompactMinus1456.small1460,CompactMinus1456.nodes1460,NodeMinus22.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1456.p1461,GridMinus.atNode 1461,GridMinus.atNode 1462,NodeMinus22.w53,CompactMinus1456.checked1461,CompactMinus1456.small1461,CompactMinus1456.nodes1461,NodeMinus22.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1456.p1462,GridMinus.atNode 1462,GridMinus.atNode 1463,NodeMinus22.w54,CompactMinus1456.checked1462,CompactMinus1456.small1462,CompactMinus1456.nodes1462,NodeMinus22.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1456.p1463,GridMinus.atNode 1463,GridMinus.atNode 1464,NodeMinus22.w55,CompactMinus1456.checked1463,CompactMinus1456.small1463,CompactMinus1456.nodes1463,NodeMinus22.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1456.p1464,GridMinus.atNode 1464,GridMinus.atNode 1465,NodeMinus22.w56,CompactMinus1456.checked1464,CompactMinus1456.small1464,CompactMinus1456.nodes1464,NodeMinus22.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1456.p1465,GridMinus.atNode 1465,GridMinus.atNode 1466,NodeMinus22.w57,CompactMinus1456.checked1465,CompactMinus1456.small1465,CompactMinus1456.nodes1465,NodeMinus22.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1456.p1466,GridMinus.atNode 1466,GridMinus.atNode 1467,NodeMinus22.w58,CompactMinus1456.checked1466,CompactMinus1456.small1466,CompactMinus1456.nodes1466,NodeMinus22.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1456.p1467,GridMinus.atNode 1467,GridMinus.atNode 1468,NodeMinus22.w59,CompactMinus1456.checked1467,CompactMinus1456.small1467,CompactMinus1456.nodes1467,NodeMinus22.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1456.p1468,GridMinus.atNode 1468,GridMinus.atNode 1469,NodeMinus22.w60,CompactMinus1456.checked1468,CompactMinus1456.small1468,CompactMinus1456.nodes1468,NodeMinus22.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1456.p1469,GridMinus.atNode 1469,GridMinus.atNode 1470,NodeMinus22.w61,CompactMinus1456.checked1469,CompactMinus1456.small1469,CompactMinus1456.nodes1469,NodeMinus22.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1456.p1470,GridMinus.atNode 1470,GridMinus.atNode 1471,NodeMinus22.w62,CompactMinus1456.checked1470,CompactMinus1456.small1470,CompactMinus1456.nodes1470,NodeMinus22.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1456.p1471,GridMinus.atNode 1471,GridMinus.atNode 1472,NodeMinus22.w63,CompactMinus1456.checked1471,CompactMinus1456.small1471,CompactMinus1456.nodes1471,NodeMinus22.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (1408+j) ∧
    (atRow j).right=GridMinus.atNode (1408+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus22
