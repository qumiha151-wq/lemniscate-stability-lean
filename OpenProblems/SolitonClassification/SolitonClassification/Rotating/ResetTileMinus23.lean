import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus1472
import SolitonClassification.Rotating.ResetPackedMinus1488
import SolitonClassification.Rotating.ResetPackedMinus1504
import SolitonClassification.Rotating.ResetPackedMinus1520
namespace SolitonClassification.Rotating.DyadicReset.TileMinus23
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1472.p1472,GridMinus.atNode 1472,GridMinus.atNode 1473,NodeMinus23.w0,CompactMinus1472.checked1472,CompactMinus1472.small1472,CompactMinus1472.nodes1472,NodeMinus23.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1472.p1473,GridMinus.atNode 1473,GridMinus.atNode 1474,NodeMinus23.w1,CompactMinus1472.checked1473,CompactMinus1472.small1473,CompactMinus1472.nodes1473,NodeMinus23.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1472.p1474,GridMinus.atNode 1474,GridMinus.atNode 1475,NodeMinus23.w2,CompactMinus1472.checked1474,CompactMinus1472.small1474,CompactMinus1472.nodes1474,NodeMinus23.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1472.p1475,GridMinus.atNode 1475,GridMinus.atNode 1476,NodeMinus23.w3,CompactMinus1472.checked1475,CompactMinus1472.small1475,CompactMinus1472.nodes1475,NodeMinus23.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1472.p1476,GridMinus.atNode 1476,GridMinus.atNode 1477,NodeMinus23.w4,CompactMinus1472.checked1476,CompactMinus1472.small1476,CompactMinus1472.nodes1476,NodeMinus23.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1472.p1477,GridMinus.atNode 1477,GridMinus.atNode 1478,NodeMinus23.w5,CompactMinus1472.checked1477,CompactMinus1472.small1477,CompactMinus1472.nodes1477,NodeMinus23.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1472.p1478,GridMinus.atNode 1478,GridMinus.atNode 1479,NodeMinus23.w6,CompactMinus1472.checked1478,CompactMinus1472.small1478,CompactMinus1472.nodes1478,NodeMinus23.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1472.p1479,GridMinus.atNode 1479,GridMinus.atNode 1480,NodeMinus23.w7,CompactMinus1472.checked1479,CompactMinus1472.small1479,CompactMinus1472.nodes1479,NodeMinus23.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1472.p1480,GridMinus.atNode 1480,GridMinus.atNode 1481,NodeMinus23.w8,CompactMinus1472.checked1480,CompactMinus1472.small1480,CompactMinus1472.nodes1480,NodeMinus23.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1472.p1481,GridMinus.atNode 1481,GridMinus.atNode 1482,NodeMinus23.w9,CompactMinus1472.checked1481,CompactMinus1472.small1481,CompactMinus1472.nodes1481,NodeMinus23.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1472.p1482,GridMinus.atNode 1482,GridMinus.atNode 1483,NodeMinus23.w10,CompactMinus1472.checked1482,CompactMinus1472.small1482,CompactMinus1472.nodes1482,NodeMinus23.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1472.p1483,GridMinus.atNode 1483,GridMinus.atNode 1484,NodeMinus23.w11,CompactMinus1472.checked1483,CompactMinus1472.small1483,CompactMinus1472.nodes1483,NodeMinus23.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1472.p1484,GridMinus.atNode 1484,GridMinus.atNode 1485,NodeMinus23.w12,CompactMinus1472.checked1484,CompactMinus1472.small1484,CompactMinus1472.nodes1484,NodeMinus23.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1472.p1485,GridMinus.atNode 1485,GridMinus.atNode 1486,NodeMinus23.w13,CompactMinus1472.checked1485,CompactMinus1472.small1485,CompactMinus1472.nodes1485,NodeMinus23.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1472.p1486,GridMinus.atNode 1486,GridMinus.atNode 1487,NodeMinus23.w14,CompactMinus1472.checked1486,CompactMinus1472.small1486,CompactMinus1472.nodes1486,NodeMinus23.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1472.p1487,GridMinus.atNode 1487,GridMinus.atNode 1488,NodeMinus23.w15,CompactMinus1472.checked1487,CompactMinus1472.small1487,CompactMinus1472.nodes1487,NodeMinus23.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1488.p1488,GridMinus.atNode 1488,GridMinus.atNode 1489,NodeMinus23.w16,CompactMinus1488.checked1488,CompactMinus1488.small1488,CompactMinus1488.nodes1488,NodeMinus23.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1488.p1489,GridMinus.atNode 1489,GridMinus.atNode 1490,NodeMinus23.w17,CompactMinus1488.checked1489,CompactMinus1488.small1489,CompactMinus1488.nodes1489,NodeMinus23.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1488.p1490,GridMinus.atNode 1490,GridMinus.atNode 1491,NodeMinus23.w18,CompactMinus1488.checked1490,CompactMinus1488.small1490,CompactMinus1488.nodes1490,NodeMinus23.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1488.p1491,GridMinus.atNode 1491,GridMinus.atNode 1492,NodeMinus23.w19,CompactMinus1488.checked1491,CompactMinus1488.small1491,CompactMinus1488.nodes1491,NodeMinus23.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1488.p1492,GridMinus.atNode 1492,GridMinus.atNode 1493,NodeMinus23.w20,CompactMinus1488.checked1492,CompactMinus1488.small1492,CompactMinus1488.nodes1492,NodeMinus23.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1488.p1493,GridMinus.atNode 1493,GridMinus.atNode 1494,NodeMinus23.w21,CompactMinus1488.checked1493,CompactMinus1488.small1493,CompactMinus1488.nodes1493,NodeMinus23.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1488.p1494,GridMinus.atNode 1494,GridMinus.atNode 1495,NodeMinus23.w22,CompactMinus1488.checked1494,CompactMinus1488.small1494,CompactMinus1488.nodes1494,NodeMinus23.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1488.p1495,GridMinus.atNode 1495,GridMinus.atNode 1496,NodeMinus23.w23,CompactMinus1488.checked1495,CompactMinus1488.small1495,CompactMinus1488.nodes1495,NodeMinus23.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1488.p1496,GridMinus.atNode 1496,GridMinus.atNode 1497,NodeMinus23.w24,CompactMinus1488.checked1496,CompactMinus1488.small1496,CompactMinus1488.nodes1496,NodeMinus23.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1488.p1497,GridMinus.atNode 1497,GridMinus.atNode 1498,NodeMinus23.w25,CompactMinus1488.checked1497,CompactMinus1488.small1497,CompactMinus1488.nodes1497,NodeMinus23.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1488.p1498,GridMinus.atNode 1498,GridMinus.atNode 1499,NodeMinus23.w26,CompactMinus1488.checked1498,CompactMinus1488.small1498,CompactMinus1488.nodes1498,NodeMinus23.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1488.p1499,GridMinus.atNode 1499,GridMinus.atNode 1500,NodeMinus23.w27,CompactMinus1488.checked1499,CompactMinus1488.small1499,CompactMinus1488.nodes1499,NodeMinus23.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1488.p1500,GridMinus.atNode 1500,GridMinus.atNode 1501,NodeMinus23.w28,CompactMinus1488.checked1500,CompactMinus1488.small1500,CompactMinus1488.nodes1500,NodeMinus23.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1488.p1501,GridMinus.atNode 1501,GridMinus.atNode 1502,NodeMinus23.w29,CompactMinus1488.checked1501,CompactMinus1488.small1501,CompactMinus1488.nodes1501,NodeMinus23.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1488.p1502,GridMinus.atNode 1502,GridMinus.atNode 1503,NodeMinus23.w30,CompactMinus1488.checked1502,CompactMinus1488.small1502,CompactMinus1488.nodes1502,NodeMinus23.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1488.p1503,GridMinus.atNode 1503,GridMinus.atNode 1504,NodeMinus23.w31,CompactMinus1488.checked1503,CompactMinus1488.small1503,CompactMinus1488.nodes1503,NodeMinus23.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1504.p1504,GridMinus.atNode 1504,GridMinus.atNode 1505,NodeMinus23.w32,CompactMinus1504.checked1504,CompactMinus1504.small1504,CompactMinus1504.nodes1504,NodeMinus23.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1504.p1505,GridMinus.atNode 1505,GridMinus.atNode 1506,NodeMinus23.w33,CompactMinus1504.checked1505,CompactMinus1504.small1505,CompactMinus1504.nodes1505,NodeMinus23.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1504.p1506,GridMinus.atNode 1506,GridMinus.atNode 1507,NodeMinus23.w34,CompactMinus1504.checked1506,CompactMinus1504.small1506,CompactMinus1504.nodes1506,NodeMinus23.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1504.p1507,GridMinus.atNode 1507,GridMinus.atNode 1508,NodeMinus23.w35,CompactMinus1504.checked1507,CompactMinus1504.small1507,CompactMinus1504.nodes1507,NodeMinus23.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1504.p1508,GridMinus.atNode 1508,GridMinus.atNode 1509,NodeMinus23.w36,CompactMinus1504.checked1508,CompactMinus1504.small1508,CompactMinus1504.nodes1508,NodeMinus23.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1504.p1509,GridMinus.atNode 1509,GridMinus.atNode 1510,NodeMinus23.w37,CompactMinus1504.checked1509,CompactMinus1504.small1509,CompactMinus1504.nodes1509,NodeMinus23.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1504.p1510,GridMinus.atNode 1510,GridMinus.atNode 1511,NodeMinus23.w38,CompactMinus1504.checked1510,CompactMinus1504.small1510,CompactMinus1504.nodes1510,NodeMinus23.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1504.p1511,GridMinus.atNode 1511,GridMinus.atNode 1512,NodeMinus23.w39,CompactMinus1504.checked1511,CompactMinus1504.small1511,CompactMinus1504.nodes1511,NodeMinus23.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1504.p1512,GridMinus.atNode 1512,GridMinus.atNode 1513,NodeMinus23.w40,CompactMinus1504.checked1512,CompactMinus1504.small1512,CompactMinus1504.nodes1512,NodeMinus23.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1504.p1513,GridMinus.atNode 1513,GridMinus.atNode 1514,NodeMinus23.w41,CompactMinus1504.checked1513,CompactMinus1504.small1513,CompactMinus1504.nodes1513,NodeMinus23.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1504.p1514,GridMinus.atNode 1514,GridMinus.atNode 1515,NodeMinus23.w42,CompactMinus1504.checked1514,CompactMinus1504.small1514,CompactMinus1504.nodes1514,NodeMinus23.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1504.p1515,GridMinus.atNode 1515,GridMinus.atNode 1516,NodeMinus23.w43,CompactMinus1504.checked1515,CompactMinus1504.small1515,CompactMinus1504.nodes1515,NodeMinus23.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1504.p1516,GridMinus.atNode 1516,GridMinus.atNode 1517,NodeMinus23.w44,CompactMinus1504.checked1516,CompactMinus1504.small1516,CompactMinus1504.nodes1516,NodeMinus23.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1504.p1517,GridMinus.atNode 1517,GridMinus.atNode 1518,NodeMinus23.w45,CompactMinus1504.checked1517,CompactMinus1504.small1517,CompactMinus1504.nodes1517,NodeMinus23.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1504.p1518,GridMinus.atNode 1518,GridMinus.atNode 1519,NodeMinus23.w46,CompactMinus1504.checked1518,CompactMinus1504.small1518,CompactMinus1504.nodes1518,NodeMinus23.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1504.p1519,GridMinus.atNode 1519,GridMinus.atNode 1520,NodeMinus23.w47,CompactMinus1504.checked1519,CompactMinus1504.small1519,CompactMinus1504.nodes1519,NodeMinus23.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1520.p1520,GridMinus.atNode 1520,GridMinus.atNode 1521,NodeMinus23.w48,CompactMinus1520.checked1520,CompactMinus1520.small1520,CompactMinus1520.nodes1520,NodeMinus23.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1520.p1521,GridMinus.atNode 1521,GridMinus.atNode 1522,NodeMinus23.w49,CompactMinus1520.checked1521,CompactMinus1520.small1521,CompactMinus1520.nodes1521,NodeMinus23.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1520.p1522,GridMinus.atNode 1522,GridMinus.atNode 1523,NodeMinus23.w50,CompactMinus1520.checked1522,CompactMinus1520.small1522,CompactMinus1520.nodes1522,NodeMinus23.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1520.p1523,GridMinus.atNode 1523,GridMinus.atNode 1524,NodeMinus23.w51,CompactMinus1520.checked1523,CompactMinus1520.small1523,CompactMinus1520.nodes1523,NodeMinus23.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1520.p1524,GridMinus.atNode 1524,GridMinus.atNode 1525,NodeMinus23.w52,CompactMinus1520.checked1524,CompactMinus1520.small1524,CompactMinus1520.nodes1524,NodeMinus23.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1520.p1525,GridMinus.atNode 1525,GridMinus.atNode 1526,NodeMinus23.w53,CompactMinus1520.checked1525,CompactMinus1520.small1525,CompactMinus1520.nodes1525,NodeMinus23.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1520.p1526,GridMinus.atNode 1526,GridMinus.atNode 1527,NodeMinus23.w54,CompactMinus1520.checked1526,CompactMinus1520.small1526,CompactMinus1520.nodes1526,NodeMinus23.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1520.p1527,GridMinus.atNode 1527,GridMinus.atNode 1528,NodeMinus23.w55,CompactMinus1520.checked1527,CompactMinus1520.small1527,CompactMinus1520.nodes1527,NodeMinus23.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1520.p1528,GridMinus.atNode 1528,GridMinus.atNode 1529,NodeMinus23.w56,CompactMinus1520.checked1528,CompactMinus1520.small1528,CompactMinus1520.nodes1528,NodeMinus23.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1520.p1529,GridMinus.atNode 1529,GridMinus.atNode 1530,NodeMinus23.w57,CompactMinus1520.checked1529,CompactMinus1520.small1529,CompactMinus1520.nodes1529,NodeMinus23.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1520.p1530,GridMinus.atNode 1530,GridMinus.atNode 1531,NodeMinus23.w58,CompactMinus1520.checked1530,CompactMinus1520.small1530,CompactMinus1520.nodes1530,NodeMinus23.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1520.p1531,GridMinus.atNode 1531,GridMinus.atNode 1532,NodeMinus23.w59,CompactMinus1520.checked1531,CompactMinus1520.small1531,CompactMinus1520.nodes1531,NodeMinus23.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1520.p1532,GridMinus.atNode 1532,GridMinus.atNode 1533,NodeMinus23.w60,CompactMinus1520.checked1532,CompactMinus1520.small1532,CompactMinus1520.nodes1532,NodeMinus23.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1520.p1533,GridMinus.atNode 1533,GridMinus.atNode 1534,NodeMinus23.w61,CompactMinus1520.checked1533,CompactMinus1520.small1533,CompactMinus1520.nodes1533,NodeMinus23.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1520.p1534,GridMinus.atNode 1534,GridMinus.atNode 1535,NodeMinus23.w62,CompactMinus1520.checked1534,CompactMinus1520.small1534,CompactMinus1520.nodes1534,NodeMinus23.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1520.p1535,GridMinus.atNode 1535,GridMinus.atNode 1536,NodeMinus23.w63,CompactMinus1520.checked1535,CompactMinus1520.small1535,CompactMinus1520.nodes1535,NodeMinus23.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (1472+j) ∧
    (atRow j).right=GridMinus.atNode (1472+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus23
