import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus1536
import SolitonClassification.Rotating.ResetPackedPlus1552
import SolitonClassification.Rotating.ResetPackedPlus1568
import SolitonClassification.Rotating.ResetPackedPlus1584
namespace SolitonClassification.Rotating.DyadicReset.TilePlus24
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus1536.p1536,GridPlus.atNode 1536,GridPlus.atNode 1537,NodePlus24.w0,CompactPlus1536.checked1536,CompactPlus1536.small1536,CompactPlus1536.nodes1536,NodePlus24.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus1536.p1537,GridPlus.atNode 1537,GridPlus.atNode 1538,NodePlus24.w1,CompactPlus1536.checked1537,CompactPlus1536.small1537,CompactPlus1536.nodes1537,NodePlus24.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus1536.p1538,GridPlus.atNode 1538,GridPlus.atNode 1539,NodePlus24.w2,CompactPlus1536.checked1538,CompactPlus1536.small1538,CompactPlus1536.nodes1538,NodePlus24.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus1536.p1539,GridPlus.atNode 1539,GridPlus.atNode 1540,NodePlus24.w3,CompactPlus1536.checked1539,CompactPlus1536.small1539,CompactPlus1536.nodes1539,NodePlus24.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus1536.p1540,GridPlus.atNode 1540,GridPlus.atNode 1541,NodePlus24.w4,CompactPlus1536.checked1540,CompactPlus1536.small1540,CompactPlus1536.nodes1540,NodePlus24.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus1536.p1541,GridPlus.atNode 1541,GridPlus.atNode 1542,NodePlus24.w5,CompactPlus1536.checked1541,CompactPlus1536.small1541,CompactPlus1536.nodes1541,NodePlus24.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus1536.p1542,GridPlus.atNode 1542,GridPlus.atNode 1543,NodePlus24.w6,CompactPlus1536.checked1542,CompactPlus1536.small1542,CompactPlus1536.nodes1542,NodePlus24.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus1536.p1543,GridPlus.atNode 1543,GridPlus.atNode 1544,NodePlus24.w7,CompactPlus1536.checked1543,CompactPlus1536.small1543,CompactPlus1536.nodes1543,NodePlus24.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus1536.p1544,GridPlus.atNode 1544,GridPlus.atNode 1545,NodePlus24.w8,CompactPlus1536.checked1544,CompactPlus1536.small1544,CompactPlus1536.nodes1544,NodePlus24.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus1536.p1545,GridPlus.atNode 1545,GridPlus.atNode 1546,NodePlus24.w9,CompactPlus1536.checked1545,CompactPlus1536.small1545,CompactPlus1536.nodes1545,NodePlus24.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus1536.p1546,GridPlus.atNode 1546,GridPlus.atNode 1547,NodePlus24.w10,CompactPlus1536.checked1546,CompactPlus1536.small1546,CompactPlus1536.nodes1546,NodePlus24.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus1536.p1547,GridPlus.atNode 1547,GridPlus.atNode 1548,NodePlus24.w11,CompactPlus1536.checked1547,CompactPlus1536.small1547,CompactPlus1536.nodes1547,NodePlus24.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus1536.p1548,GridPlus.atNode 1548,GridPlus.atNode 1549,NodePlus24.w12,CompactPlus1536.checked1548,CompactPlus1536.small1548,CompactPlus1536.nodes1548,NodePlus24.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus1536.p1549,GridPlus.atNode 1549,GridPlus.atNode 1550,NodePlus24.w13,CompactPlus1536.checked1549,CompactPlus1536.small1549,CompactPlus1536.nodes1549,NodePlus24.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus1536.p1550,GridPlus.atNode 1550,GridPlus.atNode 1551,NodePlus24.w14,CompactPlus1536.checked1550,CompactPlus1536.small1550,CompactPlus1536.nodes1550,NodePlus24.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus1536.p1551,GridPlus.atNode 1551,GridPlus.atNode 1552,NodePlus24.w15,CompactPlus1536.checked1551,CompactPlus1536.small1551,CompactPlus1536.nodes1551,NodePlus24.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus1552.p1552,GridPlus.atNode 1552,GridPlus.atNode 1553,NodePlus24.w16,CompactPlus1552.checked1552,CompactPlus1552.small1552,CompactPlus1552.nodes1552,NodePlus24.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus1552.p1553,GridPlus.atNode 1553,GridPlus.atNode 1554,NodePlus24.w17,CompactPlus1552.checked1553,CompactPlus1552.small1553,CompactPlus1552.nodes1553,NodePlus24.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus1552.p1554,GridPlus.atNode 1554,GridPlus.atNode 1555,NodePlus24.w18,CompactPlus1552.checked1554,CompactPlus1552.small1554,CompactPlus1552.nodes1554,NodePlus24.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus1552.p1555,GridPlus.atNode 1555,GridPlus.atNode 1556,NodePlus24.w19,CompactPlus1552.checked1555,CompactPlus1552.small1555,CompactPlus1552.nodes1555,NodePlus24.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus1552.p1556,GridPlus.atNode 1556,GridPlus.atNode 1557,NodePlus24.w20,CompactPlus1552.checked1556,CompactPlus1552.small1556,CompactPlus1552.nodes1556,NodePlus24.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus1552.p1557,GridPlus.atNode 1557,GridPlus.atNode 1558,NodePlus24.w21,CompactPlus1552.checked1557,CompactPlus1552.small1557,CompactPlus1552.nodes1557,NodePlus24.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus1552.p1558,GridPlus.atNode 1558,GridPlus.atNode 1559,NodePlus24.w22,CompactPlus1552.checked1558,CompactPlus1552.small1558,CompactPlus1552.nodes1558,NodePlus24.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus1552.p1559,GridPlus.atNode 1559,GridPlus.atNode 1560,NodePlus24.w23,CompactPlus1552.checked1559,CompactPlus1552.small1559,CompactPlus1552.nodes1559,NodePlus24.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus1552.p1560,GridPlus.atNode 1560,GridPlus.atNode 1561,NodePlus24.w24,CompactPlus1552.checked1560,CompactPlus1552.small1560,CompactPlus1552.nodes1560,NodePlus24.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus1552.p1561,GridPlus.atNode 1561,GridPlus.atNode 1562,NodePlus24.w25,CompactPlus1552.checked1561,CompactPlus1552.small1561,CompactPlus1552.nodes1561,NodePlus24.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus1552.p1562,GridPlus.atNode 1562,GridPlus.atNode 1563,NodePlus24.w26,CompactPlus1552.checked1562,CompactPlus1552.small1562,CompactPlus1552.nodes1562,NodePlus24.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus1552.p1563,GridPlus.atNode 1563,GridPlus.atNode 1564,NodePlus24.w27,CompactPlus1552.checked1563,CompactPlus1552.small1563,CompactPlus1552.nodes1563,NodePlus24.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus1552.p1564,GridPlus.atNode 1564,GridPlus.atNode 1565,NodePlus24.w28,CompactPlus1552.checked1564,CompactPlus1552.small1564,CompactPlus1552.nodes1564,NodePlus24.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus1552.p1565,GridPlus.atNode 1565,GridPlus.atNode 1566,NodePlus24.w29,CompactPlus1552.checked1565,CompactPlus1552.small1565,CompactPlus1552.nodes1565,NodePlus24.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus1552.p1566,GridPlus.atNode 1566,GridPlus.atNode 1567,NodePlus24.w30,CompactPlus1552.checked1566,CompactPlus1552.small1566,CompactPlus1552.nodes1566,NodePlus24.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus1552.p1567,GridPlus.atNode 1567,GridPlus.atNode 1568,NodePlus24.w31,CompactPlus1552.checked1567,CompactPlus1552.small1567,CompactPlus1552.nodes1567,NodePlus24.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus1568.p1568,GridPlus.atNode 1568,GridPlus.atNode 1569,NodePlus24.w32,CompactPlus1568.checked1568,CompactPlus1568.small1568,CompactPlus1568.nodes1568,NodePlus24.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus1568.p1569,GridPlus.atNode 1569,GridPlus.atNode 1570,NodePlus24.w33,CompactPlus1568.checked1569,CompactPlus1568.small1569,CompactPlus1568.nodes1569,NodePlus24.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus1568.p1570,GridPlus.atNode 1570,GridPlus.atNode 1571,NodePlus24.w34,CompactPlus1568.checked1570,CompactPlus1568.small1570,CompactPlus1568.nodes1570,NodePlus24.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus1568.p1571,GridPlus.atNode 1571,GridPlus.atNode 1572,NodePlus24.w35,CompactPlus1568.checked1571,CompactPlus1568.small1571,CompactPlus1568.nodes1571,NodePlus24.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus1568.p1572,GridPlus.atNode 1572,GridPlus.atNode 1573,NodePlus24.w36,CompactPlus1568.checked1572,CompactPlus1568.small1572,CompactPlus1568.nodes1572,NodePlus24.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus1568.p1573,GridPlus.atNode 1573,GridPlus.atNode 1574,NodePlus24.w37,CompactPlus1568.checked1573,CompactPlus1568.small1573,CompactPlus1568.nodes1573,NodePlus24.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus1568.p1574,GridPlus.atNode 1574,GridPlus.atNode 1575,NodePlus24.w38,CompactPlus1568.checked1574,CompactPlus1568.small1574,CompactPlus1568.nodes1574,NodePlus24.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus1568.p1575,GridPlus.atNode 1575,GridPlus.atNode 1576,NodePlus24.w39,CompactPlus1568.checked1575,CompactPlus1568.small1575,CompactPlus1568.nodes1575,NodePlus24.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus1568.p1576,GridPlus.atNode 1576,GridPlus.atNode 1577,NodePlus24.w40,CompactPlus1568.checked1576,CompactPlus1568.small1576,CompactPlus1568.nodes1576,NodePlus24.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus1568.p1577,GridPlus.atNode 1577,GridPlus.atNode 1578,NodePlus24.w41,CompactPlus1568.checked1577,CompactPlus1568.small1577,CompactPlus1568.nodes1577,NodePlus24.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus1568.p1578,GridPlus.atNode 1578,GridPlus.atNode 1579,NodePlus24.w42,CompactPlus1568.checked1578,CompactPlus1568.small1578,CompactPlus1568.nodes1578,NodePlus24.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus1568.p1579,GridPlus.atNode 1579,GridPlus.atNode 1580,NodePlus24.w43,CompactPlus1568.checked1579,CompactPlus1568.small1579,CompactPlus1568.nodes1579,NodePlus24.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus1568.p1580,GridPlus.atNode 1580,GridPlus.atNode 1581,NodePlus24.w44,CompactPlus1568.checked1580,CompactPlus1568.small1580,CompactPlus1568.nodes1580,NodePlus24.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus1568.p1581,GridPlus.atNode 1581,GridPlus.atNode 1582,NodePlus24.w45,CompactPlus1568.checked1581,CompactPlus1568.small1581,CompactPlus1568.nodes1581,NodePlus24.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus1568.p1582,GridPlus.atNode 1582,GridPlus.atNode 1583,NodePlus24.w46,CompactPlus1568.checked1582,CompactPlus1568.small1582,CompactPlus1568.nodes1582,NodePlus24.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus1568.p1583,GridPlus.atNode 1583,GridPlus.atNode 1584,NodePlus24.w47,CompactPlus1568.checked1583,CompactPlus1568.small1583,CompactPlus1568.nodes1583,NodePlus24.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus1584.p1584,GridPlus.atNode 1584,GridPlus.atNode 1585,NodePlus24.w48,CompactPlus1584.checked1584,CompactPlus1584.small1584,CompactPlus1584.nodes1584,NodePlus24.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus1584.p1585,GridPlus.atNode 1585,GridPlus.atNode 1586,NodePlus24.w49,CompactPlus1584.checked1585,CompactPlus1584.small1585,CompactPlus1584.nodes1585,NodePlus24.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus1584.p1586,GridPlus.atNode 1586,GridPlus.atNode 1587,NodePlus24.w50,CompactPlus1584.checked1586,CompactPlus1584.small1586,CompactPlus1584.nodes1586,NodePlus24.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus1584.p1587,GridPlus.atNode 1587,GridPlus.atNode 1588,NodePlus24.w51,CompactPlus1584.checked1587,CompactPlus1584.small1587,CompactPlus1584.nodes1587,NodePlus24.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus1584.p1588,GridPlus.atNode 1588,GridPlus.atNode 1589,NodePlus24.w52,CompactPlus1584.checked1588,CompactPlus1584.small1588,CompactPlus1584.nodes1588,NodePlus24.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus1584.p1589,GridPlus.atNode 1589,GridPlus.atNode 1590,NodePlus24.w53,CompactPlus1584.checked1589,CompactPlus1584.small1589,CompactPlus1584.nodes1589,NodePlus24.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus1584.p1590,GridPlus.atNode 1590,GridPlus.atNode 1591,NodePlus24.w54,CompactPlus1584.checked1590,CompactPlus1584.small1590,CompactPlus1584.nodes1590,NodePlus24.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus1584.p1591,GridPlus.atNode 1591,GridPlus.atNode 1592,NodePlus24.w55,CompactPlus1584.checked1591,CompactPlus1584.small1591,CompactPlus1584.nodes1591,NodePlus24.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus1584.p1592,GridPlus.atNode 1592,GridPlus.atNode 1593,NodePlus24.w56,CompactPlus1584.checked1592,CompactPlus1584.small1592,CompactPlus1584.nodes1592,NodePlus24.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus1584.p1593,GridPlus.atNode 1593,GridPlus.atNode 1594,NodePlus24.w57,CompactPlus1584.checked1593,CompactPlus1584.small1593,CompactPlus1584.nodes1593,NodePlus24.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus1584.p1594,GridPlus.atNode 1594,GridPlus.atNode 1595,NodePlus24.w58,CompactPlus1584.checked1594,CompactPlus1584.small1594,CompactPlus1584.nodes1594,NodePlus24.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus1584.p1595,GridPlus.atNode 1595,GridPlus.atNode 1596,NodePlus24.w59,CompactPlus1584.checked1595,CompactPlus1584.small1595,CompactPlus1584.nodes1595,NodePlus24.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus1584.p1596,GridPlus.atNode 1596,GridPlus.atNode 1597,NodePlus24.w60,CompactPlus1584.checked1596,CompactPlus1584.small1596,CompactPlus1584.nodes1596,NodePlus24.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus1584.p1597,GridPlus.atNode 1597,GridPlus.atNode 1598,NodePlus24.w61,CompactPlus1584.checked1597,CompactPlus1584.small1597,CompactPlus1584.nodes1597,NodePlus24.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus1584.p1598,GridPlus.atNode 1598,GridPlus.atNode 1599,NodePlus24.w62,CompactPlus1584.checked1598,CompactPlus1584.small1598,CompactPlus1584.nodes1598,NodePlus24.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus1584.p1599,GridPlus.atNode 1599,GridPlus.atNode 1600,NodePlus24.w63,CompactPlus1584.checked1599,CompactPlus1584.small1599,CompactPlus1584.nodes1599,NodePlus24.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (1536+j) ∧
    (atRow j).right=GridPlus.atNode (1536+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus24
