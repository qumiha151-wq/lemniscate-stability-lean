import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus1536
import SolitonClassification.Rotating.ResetPackedMinus1552
import SolitonClassification.Rotating.ResetPackedMinus1568
import SolitonClassification.Rotating.ResetPackedMinus1584
namespace SolitonClassification.Rotating.DyadicReset.TileMinus24
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1536.p1536,GridMinus.atNode 1536,GridMinus.atNode 1537,NodeMinus24.w0,CompactMinus1536.checked1536,CompactMinus1536.small1536,CompactMinus1536.nodes1536,NodeMinus24.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1536.p1537,GridMinus.atNode 1537,GridMinus.atNode 1538,NodeMinus24.w1,CompactMinus1536.checked1537,CompactMinus1536.small1537,CompactMinus1536.nodes1537,NodeMinus24.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1536.p1538,GridMinus.atNode 1538,GridMinus.atNode 1539,NodeMinus24.w2,CompactMinus1536.checked1538,CompactMinus1536.small1538,CompactMinus1536.nodes1538,NodeMinus24.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1536.p1539,GridMinus.atNode 1539,GridMinus.atNode 1540,NodeMinus24.w3,CompactMinus1536.checked1539,CompactMinus1536.small1539,CompactMinus1536.nodes1539,NodeMinus24.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1536.p1540,GridMinus.atNode 1540,GridMinus.atNode 1541,NodeMinus24.w4,CompactMinus1536.checked1540,CompactMinus1536.small1540,CompactMinus1536.nodes1540,NodeMinus24.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1536.p1541,GridMinus.atNode 1541,GridMinus.atNode 1542,NodeMinus24.w5,CompactMinus1536.checked1541,CompactMinus1536.small1541,CompactMinus1536.nodes1541,NodeMinus24.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1536.p1542,GridMinus.atNode 1542,GridMinus.atNode 1543,NodeMinus24.w6,CompactMinus1536.checked1542,CompactMinus1536.small1542,CompactMinus1536.nodes1542,NodeMinus24.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1536.p1543,GridMinus.atNode 1543,GridMinus.atNode 1544,NodeMinus24.w7,CompactMinus1536.checked1543,CompactMinus1536.small1543,CompactMinus1536.nodes1543,NodeMinus24.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1536.p1544,GridMinus.atNode 1544,GridMinus.atNode 1545,NodeMinus24.w8,CompactMinus1536.checked1544,CompactMinus1536.small1544,CompactMinus1536.nodes1544,NodeMinus24.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1536.p1545,GridMinus.atNode 1545,GridMinus.atNode 1546,NodeMinus24.w9,CompactMinus1536.checked1545,CompactMinus1536.small1545,CompactMinus1536.nodes1545,NodeMinus24.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1536.p1546,GridMinus.atNode 1546,GridMinus.atNode 1547,NodeMinus24.w10,CompactMinus1536.checked1546,CompactMinus1536.small1546,CompactMinus1536.nodes1546,NodeMinus24.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1536.p1547,GridMinus.atNode 1547,GridMinus.atNode 1548,NodeMinus24.w11,CompactMinus1536.checked1547,CompactMinus1536.small1547,CompactMinus1536.nodes1547,NodeMinus24.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1536.p1548,GridMinus.atNode 1548,GridMinus.atNode 1549,NodeMinus24.w12,CompactMinus1536.checked1548,CompactMinus1536.small1548,CompactMinus1536.nodes1548,NodeMinus24.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1536.p1549,GridMinus.atNode 1549,GridMinus.atNode 1550,NodeMinus24.w13,CompactMinus1536.checked1549,CompactMinus1536.small1549,CompactMinus1536.nodes1549,NodeMinus24.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1536.p1550,GridMinus.atNode 1550,GridMinus.atNode 1551,NodeMinus24.w14,CompactMinus1536.checked1550,CompactMinus1536.small1550,CompactMinus1536.nodes1550,NodeMinus24.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1536.p1551,GridMinus.atNode 1551,GridMinus.atNode 1552,NodeMinus24.w15,CompactMinus1536.checked1551,CompactMinus1536.small1551,CompactMinus1536.nodes1551,NodeMinus24.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1552.p1552,GridMinus.atNode 1552,GridMinus.atNode 1553,NodeMinus24.w16,CompactMinus1552.checked1552,CompactMinus1552.small1552,CompactMinus1552.nodes1552,NodeMinus24.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1552.p1553,GridMinus.atNode 1553,GridMinus.atNode 1554,NodeMinus24.w17,CompactMinus1552.checked1553,CompactMinus1552.small1553,CompactMinus1552.nodes1553,NodeMinus24.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1552.p1554,GridMinus.atNode 1554,GridMinus.atNode 1555,NodeMinus24.w18,CompactMinus1552.checked1554,CompactMinus1552.small1554,CompactMinus1552.nodes1554,NodeMinus24.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1552.p1555,GridMinus.atNode 1555,GridMinus.atNode 1556,NodeMinus24.w19,CompactMinus1552.checked1555,CompactMinus1552.small1555,CompactMinus1552.nodes1555,NodeMinus24.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1552.p1556,GridMinus.atNode 1556,GridMinus.atNode 1557,NodeMinus24.w20,CompactMinus1552.checked1556,CompactMinus1552.small1556,CompactMinus1552.nodes1556,NodeMinus24.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1552.p1557,GridMinus.atNode 1557,GridMinus.atNode 1558,NodeMinus24.w21,CompactMinus1552.checked1557,CompactMinus1552.small1557,CompactMinus1552.nodes1557,NodeMinus24.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1552.p1558,GridMinus.atNode 1558,GridMinus.atNode 1559,NodeMinus24.w22,CompactMinus1552.checked1558,CompactMinus1552.small1558,CompactMinus1552.nodes1558,NodeMinus24.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1552.p1559,GridMinus.atNode 1559,GridMinus.atNode 1560,NodeMinus24.w23,CompactMinus1552.checked1559,CompactMinus1552.small1559,CompactMinus1552.nodes1559,NodeMinus24.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1552.p1560,GridMinus.atNode 1560,GridMinus.atNode 1561,NodeMinus24.w24,CompactMinus1552.checked1560,CompactMinus1552.small1560,CompactMinus1552.nodes1560,NodeMinus24.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1552.p1561,GridMinus.atNode 1561,GridMinus.atNode 1562,NodeMinus24.w25,CompactMinus1552.checked1561,CompactMinus1552.small1561,CompactMinus1552.nodes1561,NodeMinus24.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1552.p1562,GridMinus.atNode 1562,GridMinus.atNode 1563,NodeMinus24.w26,CompactMinus1552.checked1562,CompactMinus1552.small1562,CompactMinus1552.nodes1562,NodeMinus24.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1552.p1563,GridMinus.atNode 1563,GridMinus.atNode 1564,NodeMinus24.w27,CompactMinus1552.checked1563,CompactMinus1552.small1563,CompactMinus1552.nodes1563,NodeMinus24.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1552.p1564,GridMinus.atNode 1564,GridMinus.atNode 1565,NodeMinus24.w28,CompactMinus1552.checked1564,CompactMinus1552.small1564,CompactMinus1552.nodes1564,NodeMinus24.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1552.p1565,GridMinus.atNode 1565,GridMinus.atNode 1566,NodeMinus24.w29,CompactMinus1552.checked1565,CompactMinus1552.small1565,CompactMinus1552.nodes1565,NodeMinus24.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1552.p1566,GridMinus.atNode 1566,GridMinus.atNode 1567,NodeMinus24.w30,CompactMinus1552.checked1566,CompactMinus1552.small1566,CompactMinus1552.nodes1566,NodeMinus24.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1552.p1567,GridMinus.atNode 1567,GridMinus.atNode 1568,NodeMinus24.w31,CompactMinus1552.checked1567,CompactMinus1552.small1567,CompactMinus1552.nodes1567,NodeMinus24.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1568.p1568,GridMinus.atNode 1568,GridMinus.atNode 1569,NodeMinus24.w32,CompactMinus1568.checked1568,CompactMinus1568.small1568,CompactMinus1568.nodes1568,NodeMinus24.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1568.p1569,GridMinus.atNode 1569,GridMinus.atNode 1570,NodeMinus24.w33,CompactMinus1568.checked1569,CompactMinus1568.small1569,CompactMinus1568.nodes1569,NodeMinus24.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1568.p1570,GridMinus.atNode 1570,GridMinus.atNode 1571,NodeMinus24.w34,CompactMinus1568.checked1570,CompactMinus1568.small1570,CompactMinus1568.nodes1570,NodeMinus24.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1568.p1571,GridMinus.atNode 1571,GridMinus.atNode 1572,NodeMinus24.w35,CompactMinus1568.checked1571,CompactMinus1568.small1571,CompactMinus1568.nodes1571,NodeMinus24.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1568.p1572,GridMinus.atNode 1572,GridMinus.atNode 1573,NodeMinus24.w36,CompactMinus1568.checked1572,CompactMinus1568.small1572,CompactMinus1568.nodes1572,NodeMinus24.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1568.p1573,GridMinus.atNode 1573,GridMinus.atNode 1574,NodeMinus24.w37,CompactMinus1568.checked1573,CompactMinus1568.small1573,CompactMinus1568.nodes1573,NodeMinus24.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1568.p1574,GridMinus.atNode 1574,GridMinus.atNode 1575,NodeMinus24.w38,CompactMinus1568.checked1574,CompactMinus1568.small1574,CompactMinus1568.nodes1574,NodeMinus24.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1568.p1575,GridMinus.atNode 1575,GridMinus.atNode 1576,NodeMinus24.w39,CompactMinus1568.checked1575,CompactMinus1568.small1575,CompactMinus1568.nodes1575,NodeMinus24.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1568.p1576,GridMinus.atNode 1576,GridMinus.atNode 1577,NodeMinus24.w40,CompactMinus1568.checked1576,CompactMinus1568.small1576,CompactMinus1568.nodes1576,NodeMinus24.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1568.p1577,GridMinus.atNode 1577,GridMinus.atNode 1578,NodeMinus24.w41,CompactMinus1568.checked1577,CompactMinus1568.small1577,CompactMinus1568.nodes1577,NodeMinus24.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1568.p1578,GridMinus.atNode 1578,GridMinus.atNode 1579,NodeMinus24.w42,CompactMinus1568.checked1578,CompactMinus1568.small1578,CompactMinus1568.nodes1578,NodeMinus24.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1568.p1579,GridMinus.atNode 1579,GridMinus.atNode 1580,NodeMinus24.w43,CompactMinus1568.checked1579,CompactMinus1568.small1579,CompactMinus1568.nodes1579,NodeMinus24.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1568.p1580,GridMinus.atNode 1580,GridMinus.atNode 1581,NodeMinus24.w44,CompactMinus1568.checked1580,CompactMinus1568.small1580,CompactMinus1568.nodes1580,NodeMinus24.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1568.p1581,GridMinus.atNode 1581,GridMinus.atNode 1582,NodeMinus24.w45,CompactMinus1568.checked1581,CompactMinus1568.small1581,CompactMinus1568.nodes1581,NodeMinus24.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1568.p1582,GridMinus.atNode 1582,GridMinus.atNode 1583,NodeMinus24.w46,CompactMinus1568.checked1582,CompactMinus1568.small1582,CompactMinus1568.nodes1582,NodeMinus24.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1568.p1583,GridMinus.atNode 1583,GridMinus.atNode 1584,NodeMinus24.w47,CompactMinus1568.checked1583,CompactMinus1568.small1583,CompactMinus1568.nodes1583,NodeMinus24.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1584.p1584,GridMinus.atNode 1584,GridMinus.atNode 1585,NodeMinus24.w48,CompactMinus1584.checked1584,CompactMinus1584.small1584,CompactMinus1584.nodes1584,NodeMinus24.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1584.p1585,GridMinus.atNode 1585,GridMinus.atNode 1586,NodeMinus24.w49,CompactMinus1584.checked1585,CompactMinus1584.small1585,CompactMinus1584.nodes1585,NodeMinus24.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1584.p1586,GridMinus.atNode 1586,GridMinus.atNode 1587,NodeMinus24.w50,CompactMinus1584.checked1586,CompactMinus1584.small1586,CompactMinus1584.nodes1586,NodeMinus24.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1584.p1587,GridMinus.atNode 1587,GridMinus.atNode 1588,NodeMinus24.w51,CompactMinus1584.checked1587,CompactMinus1584.small1587,CompactMinus1584.nodes1587,NodeMinus24.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1584.p1588,GridMinus.atNode 1588,GridMinus.atNode 1589,NodeMinus24.w52,CompactMinus1584.checked1588,CompactMinus1584.small1588,CompactMinus1584.nodes1588,NodeMinus24.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1584.p1589,GridMinus.atNode 1589,GridMinus.atNode 1590,NodeMinus24.w53,CompactMinus1584.checked1589,CompactMinus1584.small1589,CompactMinus1584.nodes1589,NodeMinus24.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1584.p1590,GridMinus.atNode 1590,GridMinus.atNode 1591,NodeMinus24.w54,CompactMinus1584.checked1590,CompactMinus1584.small1590,CompactMinus1584.nodes1590,NodeMinus24.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1584.p1591,GridMinus.atNode 1591,GridMinus.atNode 1592,NodeMinus24.w55,CompactMinus1584.checked1591,CompactMinus1584.small1591,CompactMinus1584.nodes1591,NodeMinus24.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1584.p1592,GridMinus.atNode 1592,GridMinus.atNode 1593,NodeMinus24.w56,CompactMinus1584.checked1592,CompactMinus1584.small1592,CompactMinus1584.nodes1592,NodeMinus24.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1584.p1593,GridMinus.atNode 1593,GridMinus.atNode 1594,NodeMinus24.w57,CompactMinus1584.checked1593,CompactMinus1584.small1593,CompactMinus1584.nodes1593,NodeMinus24.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1584.p1594,GridMinus.atNode 1594,GridMinus.atNode 1595,NodeMinus24.w58,CompactMinus1584.checked1594,CompactMinus1584.small1594,CompactMinus1584.nodes1594,NodeMinus24.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1584.p1595,GridMinus.atNode 1595,GridMinus.atNode 1596,NodeMinus24.w59,CompactMinus1584.checked1595,CompactMinus1584.small1595,CompactMinus1584.nodes1595,NodeMinus24.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1584.p1596,GridMinus.atNode 1596,GridMinus.atNode 1597,NodeMinus24.w60,CompactMinus1584.checked1596,CompactMinus1584.small1596,CompactMinus1584.nodes1596,NodeMinus24.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1584.p1597,GridMinus.atNode 1597,GridMinus.atNode 1598,NodeMinus24.w61,CompactMinus1584.checked1597,CompactMinus1584.small1597,CompactMinus1584.nodes1597,NodeMinus24.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1584.p1598,GridMinus.atNode 1598,GridMinus.atNode 1599,NodeMinus24.w62,CompactMinus1584.checked1598,CompactMinus1584.small1598,CompactMinus1584.nodes1598,NodeMinus24.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1584.p1599,GridMinus.atNode 1599,GridMinus.atNode 1600,NodeMinus24.w63,CompactMinus1584.checked1599,CompactMinus1584.small1599,CompactMinus1584.nodes1599,NodeMinus24.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (1536+j) ∧
    (atRow j).right=GridMinus.atNode (1536+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus24
