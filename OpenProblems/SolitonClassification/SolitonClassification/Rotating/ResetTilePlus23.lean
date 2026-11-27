import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus1472
import SolitonClassification.Rotating.ResetPackedPlus1488
import SolitonClassification.Rotating.ResetPackedPlus1504
import SolitonClassification.Rotating.ResetPackedPlus1520
namespace SolitonClassification.Rotating.DyadicReset.TilePlus23
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus1472.p1472,GridPlus.atNode 1472,GridPlus.atNode 1473,NodePlus23.w0,CompactPlus1472.checked1472,CompactPlus1472.small1472,CompactPlus1472.nodes1472,NodePlus23.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus1472.p1473,GridPlus.atNode 1473,GridPlus.atNode 1474,NodePlus23.w1,CompactPlus1472.checked1473,CompactPlus1472.small1473,CompactPlus1472.nodes1473,NodePlus23.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus1472.p1474,GridPlus.atNode 1474,GridPlus.atNode 1475,NodePlus23.w2,CompactPlus1472.checked1474,CompactPlus1472.small1474,CompactPlus1472.nodes1474,NodePlus23.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus1472.p1475,GridPlus.atNode 1475,GridPlus.atNode 1476,NodePlus23.w3,CompactPlus1472.checked1475,CompactPlus1472.small1475,CompactPlus1472.nodes1475,NodePlus23.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus1472.p1476,GridPlus.atNode 1476,GridPlus.atNode 1477,NodePlus23.w4,CompactPlus1472.checked1476,CompactPlus1472.small1476,CompactPlus1472.nodes1476,NodePlus23.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus1472.p1477,GridPlus.atNode 1477,GridPlus.atNode 1478,NodePlus23.w5,CompactPlus1472.checked1477,CompactPlus1472.small1477,CompactPlus1472.nodes1477,NodePlus23.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus1472.p1478,GridPlus.atNode 1478,GridPlus.atNode 1479,NodePlus23.w6,CompactPlus1472.checked1478,CompactPlus1472.small1478,CompactPlus1472.nodes1478,NodePlus23.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus1472.p1479,GridPlus.atNode 1479,GridPlus.atNode 1480,NodePlus23.w7,CompactPlus1472.checked1479,CompactPlus1472.small1479,CompactPlus1472.nodes1479,NodePlus23.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus1472.p1480,GridPlus.atNode 1480,GridPlus.atNode 1481,NodePlus23.w8,CompactPlus1472.checked1480,CompactPlus1472.small1480,CompactPlus1472.nodes1480,NodePlus23.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus1472.p1481,GridPlus.atNode 1481,GridPlus.atNode 1482,NodePlus23.w9,CompactPlus1472.checked1481,CompactPlus1472.small1481,CompactPlus1472.nodes1481,NodePlus23.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus1472.p1482,GridPlus.atNode 1482,GridPlus.atNode 1483,NodePlus23.w10,CompactPlus1472.checked1482,CompactPlus1472.small1482,CompactPlus1472.nodes1482,NodePlus23.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus1472.p1483,GridPlus.atNode 1483,GridPlus.atNode 1484,NodePlus23.w11,CompactPlus1472.checked1483,CompactPlus1472.small1483,CompactPlus1472.nodes1483,NodePlus23.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus1472.p1484,GridPlus.atNode 1484,GridPlus.atNode 1485,NodePlus23.w12,CompactPlus1472.checked1484,CompactPlus1472.small1484,CompactPlus1472.nodes1484,NodePlus23.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus1472.p1485,GridPlus.atNode 1485,GridPlus.atNode 1486,NodePlus23.w13,CompactPlus1472.checked1485,CompactPlus1472.small1485,CompactPlus1472.nodes1485,NodePlus23.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus1472.p1486,GridPlus.atNode 1486,GridPlus.atNode 1487,NodePlus23.w14,CompactPlus1472.checked1486,CompactPlus1472.small1486,CompactPlus1472.nodes1486,NodePlus23.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus1472.p1487,GridPlus.atNode 1487,GridPlus.atNode 1488,NodePlus23.w15,CompactPlus1472.checked1487,CompactPlus1472.small1487,CompactPlus1472.nodes1487,NodePlus23.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus1488.p1488,GridPlus.atNode 1488,GridPlus.atNode 1489,NodePlus23.w16,CompactPlus1488.checked1488,CompactPlus1488.small1488,CompactPlus1488.nodes1488,NodePlus23.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus1488.p1489,GridPlus.atNode 1489,GridPlus.atNode 1490,NodePlus23.w17,CompactPlus1488.checked1489,CompactPlus1488.small1489,CompactPlus1488.nodes1489,NodePlus23.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus1488.p1490,GridPlus.atNode 1490,GridPlus.atNode 1491,NodePlus23.w18,CompactPlus1488.checked1490,CompactPlus1488.small1490,CompactPlus1488.nodes1490,NodePlus23.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus1488.p1491,GridPlus.atNode 1491,GridPlus.atNode 1492,NodePlus23.w19,CompactPlus1488.checked1491,CompactPlus1488.small1491,CompactPlus1488.nodes1491,NodePlus23.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus1488.p1492,GridPlus.atNode 1492,GridPlus.atNode 1493,NodePlus23.w20,CompactPlus1488.checked1492,CompactPlus1488.small1492,CompactPlus1488.nodes1492,NodePlus23.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus1488.p1493,GridPlus.atNode 1493,GridPlus.atNode 1494,NodePlus23.w21,CompactPlus1488.checked1493,CompactPlus1488.small1493,CompactPlus1488.nodes1493,NodePlus23.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus1488.p1494,GridPlus.atNode 1494,GridPlus.atNode 1495,NodePlus23.w22,CompactPlus1488.checked1494,CompactPlus1488.small1494,CompactPlus1488.nodes1494,NodePlus23.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus1488.p1495,GridPlus.atNode 1495,GridPlus.atNode 1496,NodePlus23.w23,CompactPlus1488.checked1495,CompactPlus1488.small1495,CompactPlus1488.nodes1495,NodePlus23.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus1488.p1496,GridPlus.atNode 1496,GridPlus.atNode 1497,NodePlus23.w24,CompactPlus1488.checked1496,CompactPlus1488.small1496,CompactPlus1488.nodes1496,NodePlus23.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus1488.p1497,GridPlus.atNode 1497,GridPlus.atNode 1498,NodePlus23.w25,CompactPlus1488.checked1497,CompactPlus1488.small1497,CompactPlus1488.nodes1497,NodePlus23.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus1488.p1498,GridPlus.atNode 1498,GridPlus.atNode 1499,NodePlus23.w26,CompactPlus1488.checked1498,CompactPlus1488.small1498,CompactPlus1488.nodes1498,NodePlus23.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus1488.p1499,GridPlus.atNode 1499,GridPlus.atNode 1500,NodePlus23.w27,CompactPlus1488.checked1499,CompactPlus1488.small1499,CompactPlus1488.nodes1499,NodePlus23.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus1488.p1500,GridPlus.atNode 1500,GridPlus.atNode 1501,NodePlus23.w28,CompactPlus1488.checked1500,CompactPlus1488.small1500,CompactPlus1488.nodes1500,NodePlus23.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus1488.p1501,GridPlus.atNode 1501,GridPlus.atNode 1502,NodePlus23.w29,CompactPlus1488.checked1501,CompactPlus1488.small1501,CompactPlus1488.nodes1501,NodePlus23.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus1488.p1502,GridPlus.atNode 1502,GridPlus.atNode 1503,NodePlus23.w30,CompactPlus1488.checked1502,CompactPlus1488.small1502,CompactPlus1488.nodes1502,NodePlus23.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus1488.p1503,GridPlus.atNode 1503,GridPlus.atNode 1504,NodePlus23.w31,CompactPlus1488.checked1503,CompactPlus1488.small1503,CompactPlus1488.nodes1503,NodePlus23.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus1504.p1504,GridPlus.atNode 1504,GridPlus.atNode 1505,NodePlus23.w32,CompactPlus1504.checked1504,CompactPlus1504.small1504,CompactPlus1504.nodes1504,NodePlus23.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus1504.p1505,GridPlus.atNode 1505,GridPlus.atNode 1506,NodePlus23.w33,CompactPlus1504.checked1505,CompactPlus1504.small1505,CompactPlus1504.nodes1505,NodePlus23.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus1504.p1506,GridPlus.atNode 1506,GridPlus.atNode 1507,NodePlus23.w34,CompactPlus1504.checked1506,CompactPlus1504.small1506,CompactPlus1504.nodes1506,NodePlus23.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus1504.p1507,GridPlus.atNode 1507,GridPlus.atNode 1508,NodePlus23.w35,CompactPlus1504.checked1507,CompactPlus1504.small1507,CompactPlus1504.nodes1507,NodePlus23.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus1504.p1508,GridPlus.atNode 1508,GridPlus.atNode 1509,NodePlus23.w36,CompactPlus1504.checked1508,CompactPlus1504.small1508,CompactPlus1504.nodes1508,NodePlus23.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus1504.p1509,GridPlus.atNode 1509,GridPlus.atNode 1510,NodePlus23.w37,CompactPlus1504.checked1509,CompactPlus1504.small1509,CompactPlus1504.nodes1509,NodePlus23.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus1504.p1510,GridPlus.atNode 1510,GridPlus.atNode 1511,NodePlus23.w38,CompactPlus1504.checked1510,CompactPlus1504.small1510,CompactPlus1504.nodes1510,NodePlus23.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus1504.p1511,GridPlus.atNode 1511,GridPlus.atNode 1512,NodePlus23.w39,CompactPlus1504.checked1511,CompactPlus1504.small1511,CompactPlus1504.nodes1511,NodePlus23.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus1504.p1512,GridPlus.atNode 1512,GridPlus.atNode 1513,NodePlus23.w40,CompactPlus1504.checked1512,CompactPlus1504.small1512,CompactPlus1504.nodes1512,NodePlus23.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus1504.p1513,GridPlus.atNode 1513,GridPlus.atNode 1514,NodePlus23.w41,CompactPlus1504.checked1513,CompactPlus1504.small1513,CompactPlus1504.nodes1513,NodePlus23.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus1504.p1514,GridPlus.atNode 1514,GridPlus.atNode 1515,NodePlus23.w42,CompactPlus1504.checked1514,CompactPlus1504.small1514,CompactPlus1504.nodes1514,NodePlus23.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus1504.p1515,GridPlus.atNode 1515,GridPlus.atNode 1516,NodePlus23.w43,CompactPlus1504.checked1515,CompactPlus1504.small1515,CompactPlus1504.nodes1515,NodePlus23.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus1504.p1516,GridPlus.atNode 1516,GridPlus.atNode 1517,NodePlus23.w44,CompactPlus1504.checked1516,CompactPlus1504.small1516,CompactPlus1504.nodes1516,NodePlus23.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus1504.p1517,GridPlus.atNode 1517,GridPlus.atNode 1518,NodePlus23.w45,CompactPlus1504.checked1517,CompactPlus1504.small1517,CompactPlus1504.nodes1517,NodePlus23.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus1504.p1518,GridPlus.atNode 1518,GridPlus.atNode 1519,NodePlus23.w46,CompactPlus1504.checked1518,CompactPlus1504.small1518,CompactPlus1504.nodes1518,NodePlus23.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus1504.p1519,GridPlus.atNode 1519,GridPlus.atNode 1520,NodePlus23.w47,CompactPlus1504.checked1519,CompactPlus1504.small1519,CompactPlus1504.nodes1519,NodePlus23.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus1520.p1520,GridPlus.atNode 1520,GridPlus.atNode 1521,NodePlus23.w48,CompactPlus1520.checked1520,CompactPlus1520.small1520,CompactPlus1520.nodes1520,NodePlus23.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus1520.p1521,GridPlus.atNode 1521,GridPlus.atNode 1522,NodePlus23.w49,CompactPlus1520.checked1521,CompactPlus1520.small1521,CompactPlus1520.nodes1521,NodePlus23.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus1520.p1522,GridPlus.atNode 1522,GridPlus.atNode 1523,NodePlus23.w50,CompactPlus1520.checked1522,CompactPlus1520.small1522,CompactPlus1520.nodes1522,NodePlus23.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus1520.p1523,GridPlus.atNode 1523,GridPlus.atNode 1524,NodePlus23.w51,CompactPlus1520.checked1523,CompactPlus1520.small1523,CompactPlus1520.nodes1523,NodePlus23.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus1520.p1524,GridPlus.atNode 1524,GridPlus.atNode 1525,NodePlus23.w52,CompactPlus1520.checked1524,CompactPlus1520.small1524,CompactPlus1520.nodes1524,NodePlus23.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus1520.p1525,GridPlus.atNode 1525,GridPlus.atNode 1526,NodePlus23.w53,CompactPlus1520.checked1525,CompactPlus1520.small1525,CompactPlus1520.nodes1525,NodePlus23.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus1520.p1526,GridPlus.atNode 1526,GridPlus.atNode 1527,NodePlus23.w54,CompactPlus1520.checked1526,CompactPlus1520.small1526,CompactPlus1520.nodes1526,NodePlus23.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus1520.p1527,GridPlus.atNode 1527,GridPlus.atNode 1528,NodePlus23.w55,CompactPlus1520.checked1527,CompactPlus1520.small1527,CompactPlus1520.nodes1527,NodePlus23.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus1520.p1528,GridPlus.atNode 1528,GridPlus.atNode 1529,NodePlus23.w56,CompactPlus1520.checked1528,CompactPlus1520.small1528,CompactPlus1520.nodes1528,NodePlus23.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus1520.p1529,GridPlus.atNode 1529,GridPlus.atNode 1530,NodePlus23.w57,CompactPlus1520.checked1529,CompactPlus1520.small1529,CompactPlus1520.nodes1529,NodePlus23.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus1520.p1530,GridPlus.atNode 1530,GridPlus.atNode 1531,NodePlus23.w58,CompactPlus1520.checked1530,CompactPlus1520.small1530,CompactPlus1520.nodes1530,NodePlus23.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus1520.p1531,GridPlus.atNode 1531,GridPlus.atNode 1532,NodePlus23.w59,CompactPlus1520.checked1531,CompactPlus1520.small1531,CompactPlus1520.nodes1531,NodePlus23.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus1520.p1532,GridPlus.atNode 1532,GridPlus.atNode 1533,NodePlus23.w60,CompactPlus1520.checked1532,CompactPlus1520.small1532,CompactPlus1520.nodes1532,NodePlus23.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus1520.p1533,GridPlus.atNode 1533,GridPlus.atNode 1534,NodePlus23.w61,CompactPlus1520.checked1533,CompactPlus1520.small1533,CompactPlus1520.nodes1533,NodePlus23.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus1520.p1534,GridPlus.atNode 1534,GridPlus.atNode 1535,NodePlus23.w62,CompactPlus1520.checked1534,CompactPlus1520.small1534,CompactPlus1520.nodes1534,NodePlus23.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus1520.p1535,GridPlus.atNode 1535,GridPlus.atNode 1536,NodePlus23.w63,CompactPlus1520.checked1535,CompactPlus1520.small1535,CompactPlus1520.nodes1535,NodePlus23.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (1472+j) ∧
    (atRow j).right=GridPlus.atNode (1472+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus23
