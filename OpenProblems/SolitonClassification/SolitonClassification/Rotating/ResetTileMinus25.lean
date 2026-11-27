import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus1600
import SolitonClassification.Rotating.ResetPackedMinus1616
import SolitonClassification.Rotating.ResetPackedMinus1632
import SolitonClassification.Rotating.ResetPackedMinus1648
namespace SolitonClassification.Rotating.DyadicReset.TileMinus25
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1600.p1600,GridMinus.atNode 1600,GridMinus.atNode 1601,NodeMinus25.w0,CompactMinus1600.checked1600,CompactMinus1600.small1600,CompactMinus1600.nodes1600,NodeMinus25.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1600.p1601,GridMinus.atNode 1601,GridMinus.atNode 1602,NodeMinus25.w1,CompactMinus1600.checked1601,CompactMinus1600.small1601,CompactMinus1600.nodes1601,NodeMinus25.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1600.p1602,GridMinus.atNode 1602,GridMinus.atNode 1603,NodeMinus25.w2,CompactMinus1600.checked1602,CompactMinus1600.small1602,CompactMinus1600.nodes1602,NodeMinus25.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1600.p1603,GridMinus.atNode 1603,GridMinus.atNode 1604,NodeMinus25.w3,CompactMinus1600.checked1603,CompactMinus1600.small1603,CompactMinus1600.nodes1603,NodeMinus25.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1600.p1604,GridMinus.atNode 1604,GridMinus.atNode 1605,NodeMinus25.w4,CompactMinus1600.checked1604,CompactMinus1600.small1604,CompactMinus1600.nodes1604,NodeMinus25.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1600.p1605,GridMinus.atNode 1605,GridMinus.atNode 1606,NodeMinus25.w5,CompactMinus1600.checked1605,CompactMinus1600.small1605,CompactMinus1600.nodes1605,NodeMinus25.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1600.p1606,GridMinus.atNode 1606,GridMinus.atNode 1607,NodeMinus25.w6,CompactMinus1600.checked1606,CompactMinus1600.small1606,CompactMinus1600.nodes1606,NodeMinus25.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1600.p1607,GridMinus.atNode 1607,GridMinus.atNode 1608,NodeMinus25.w7,CompactMinus1600.checked1607,CompactMinus1600.small1607,CompactMinus1600.nodes1607,NodeMinus25.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1600.p1608,GridMinus.atNode 1608,GridMinus.atNode 1609,NodeMinus25.w8,CompactMinus1600.checked1608,CompactMinus1600.small1608,CompactMinus1600.nodes1608,NodeMinus25.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1600.p1609,GridMinus.atNode 1609,GridMinus.atNode 1610,NodeMinus25.w9,CompactMinus1600.checked1609,CompactMinus1600.small1609,CompactMinus1600.nodes1609,NodeMinus25.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1600.p1610,GridMinus.atNode 1610,GridMinus.atNode 1611,NodeMinus25.w10,CompactMinus1600.checked1610,CompactMinus1600.small1610,CompactMinus1600.nodes1610,NodeMinus25.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1600.p1611,GridMinus.atNode 1611,GridMinus.atNode 1612,NodeMinus25.w11,CompactMinus1600.checked1611,CompactMinus1600.small1611,CompactMinus1600.nodes1611,NodeMinus25.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1600.p1612,GridMinus.atNode 1612,GridMinus.atNode 1613,NodeMinus25.w12,CompactMinus1600.checked1612,CompactMinus1600.small1612,CompactMinus1600.nodes1612,NodeMinus25.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1600.p1613,GridMinus.atNode 1613,GridMinus.atNode 1614,NodeMinus25.w13,CompactMinus1600.checked1613,CompactMinus1600.small1613,CompactMinus1600.nodes1613,NodeMinus25.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1600.p1614,GridMinus.atNode 1614,GridMinus.atNode 1615,NodeMinus25.w14,CompactMinus1600.checked1614,CompactMinus1600.small1614,CompactMinus1600.nodes1614,NodeMinus25.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1600.p1615,GridMinus.atNode 1615,GridMinus.atNode 1616,NodeMinus25.w15,CompactMinus1600.checked1615,CompactMinus1600.small1615,CompactMinus1600.nodes1615,NodeMinus25.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1616.p1616,GridMinus.atNode 1616,GridMinus.atNode 1617,NodeMinus25.w16,CompactMinus1616.checked1616,CompactMinus1616.small1616,CompactMinus1616.nodes1616,NodeMinus25.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1616.p1617,GridMinus.atNode 1617,GridMinus.atNode 1618,NodeMinus25.w17,CompactMinus1616.checked1617,CompactMinus1616.small1617,CompactMinus1616.nodes1617,NodeMinus25.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1616.p1618,GridMinus.atNode 1618,GridMinus.atNode 1619,NodeMinus25.w18,CompactMinus1616.checked1618,CompactMinus1616.small1618,CompactMinus1616.nodes1618,NodeMinus25.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1616.p1619,GridMinus.atNode 1619,GridMinus.atNode 1620,NodeMinus25.w19,CompactMinus1616.checked1619,CompactMinus1616.small1619,CompactMinus1616.nodes1619,NodeMinus25.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1616.p1620,GridMinus.atNode 1620,GridMinus.atNode 1621,NodeMinus25.w20,CompactMinus1616.checked1620,CompactMinus1616.small1620,CompactMinus1616.nodes1620,NodeMinus25.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1616.p1621,GridMinus.atNode 1621,GridMinus.atNode 1622,NodeMinus25.w21,CompactMinus1616.checked1621,CompactMinus1616.small1621,CompactMinus1616.nodes1621,NodeMinus25.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1616.p1622,GridMinus.atNode 1622,GridMinus.atNode 1623,NodeMinus25.w22,CompactMinus1616.checked1622,CompactMinus1616.small1622,CompactMinus1616.nodes1622,NodeMinus25.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1616.p1623,GridMinus.atNode 1623,GridMinus.atNode 1624,NodeMinus25.w23,CompactMinus1616.checked1623,CompactMinus1616.small1623,CompactMinus1616.nodes1623,NodeMinus25.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1616.p1624,GridMinus.atNode 1624,GridMinus.atNode 1625,NodeMinus25.w24,CompactMinus1616.checked1624,CompactMinus1616.small1624,CompactMinus1616.nodes1624,NodeMinus25.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1616.p1625,GridMinus.atNode 1625,GridMinus.atNode 1626,NodeMinus25.w25,CompactMinus1616.checked1625,CompactMinus1616.small1625,CompactMinus1616.nodes1625,NodeMinus25.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1616.p1626,GridMinus.atNode 1626,GridMinus.atNode 1627,NodeMinus25.w26,CompactMinus1616.checked1626,CompactMinus1616.small1626,CompactMinus1616.nodes1626,NodeMinus25.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1616.p1627,GridMinus.atNode 1627,GridMinus.atNode 1628,NodeMinus25.w27,CompactMinus1616.checked1627,CompactMinus1616.small1627,CompactMinus1616.nodes1627,NodeMinus25.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1616.p1628,GridMinus.atNode 1628,GridMinus.atNode 1629,NodeMinus25.w28,CompactMinus1616.checked1628,CompactMinus1616.small1628,CompactMinus1616.nodes1628,NodeMinus25.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1616.p1629,GridMinus.atNode 1629,GridMinus.atNode 1630,NodeMinus25.w29,CompactMinus1616.checked1629,CompactMinus1616.small1629,CompactMinus1616.nodes1629,NodeMinus25.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1616.p1630,GridMinus.atNode 1630,GridMinus.atNode 1631,NodeMinus25.w30,CompactMinus1616.checked1630,CompactMinus1616.small1630,CompactMinus1616.nodes1630,NodeMinus25.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1616.p1631,GridMinus.atNode 1631,GridMinus.atNode 1632,NodeMinus25.w31,CompactMinus1616.checked1631,CompactMinus1616.small1631,CompactMinus1616.nodes1631,NodeMinus25.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1632.p1632,GridMinus.atNode 1632,GridMinus.atNode 1633,NodeMinus25.w32,CompactMinus1632.checked1632,CompactMinus1632.small1632,CompactMinus1632.nodes1632,NodeMinus25.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1632.p1633,GridMinus.atNode 1633,GridMinus.atNode 1634,NodeMinus25.w33,CompactMinus1632.checked1633,CompactMinus1632.small1633,CompactMinus1632.nodes1633,NodeMinus25.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1632.p1634,GridMinus.atNode 1634,GridMinus.atNode 1635,NodeMinus25.w34,CompactMinus1632.checked1634,CompactMinus1632.small1634,CompactMinus1632.nodes1634,NodeMinus25.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1632.p1635,GridMinus.atNode 1635,GridMinus.atNode 1636,NodeMinus25.w35,CompactMinus1632.checked1635,CompactMinus1632.small1635,CompactMinus1632.nodes1635,NodeMinus25.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1632.p1636,GridMinus.atNode 1636,GridMinus.atNode 1637,NodeMinus25.w36,CompactMinus1632.checked1636,CompactMinus1632.small1636,CompactMinus1632.nodes1636,NodeMinus25.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1632.p1637,GridMinus.atNode 1637,GridMinus.atNode 1638,NodeMinus25.w37,CompactMinus1632.checked1637,CompactMinus1632.small1637,CompactMinus1632.nodes1637,NodeMinus25.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1632.p1638,GridMinus.atNode 1638,GridMinus.atNode 1639,NodeMinus25.w38,CompactMinus1632.checked1638,CompactMinus1632.small1638,CompactMinus1632.nodes1638,NodeMinus25.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1632.p1639,GridMinus.atNode 1639,GridMinus.atNode 1640,NodeMinus25.w39,CompactMinus1632.checked1639,CompactMinus1632.small1639,CompactMinus1632.nodes1639,NodeMinus25.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1632.p1640,GridMinus.atNode 1640,GridMinus.atNode 1641,NodeMinus25.w40,CompactMinus1632.checked1640,CompactMinus1632.small1640,CompactMinus1632.nodes1640,NodeMinus25.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1632.p1641,GridMinus.atNode 1641,GridMinus.atNode 1642,NodeMinus25.w41,CompactMinus1632.checked1641,CompactMinus1632.small1641,CompactMinus1632.nodes1641,NodeMinus25.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1632.p1642,GridMinus.atNode 1642,GridMinus.atNode 1643,NodeMinus25.w42,CompactMinus1632.checked1642,CompactMinus1632.small1642,CompactMinus1632.nodes1642,NodeMinus25.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1632.p1643,GridMinus.atNode 1643,GridMinus.atNode 1644,NodeMinus25.w43,CompactMinus1632.checked1643,CompactMinus1632.small1643,CompactMinus1632.nodes1643,NodeMinus25.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1632.p1644,GridMinus.atNode 1644,GridMinus.atNode 1645,NodeMinus25.w44,CompactMinus1632.checked1644,CompactMinus1632.small1644,CompactMinus1632.nodes1644,NodeMinus25.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1632.p1645,GridMinus.atNode 1645,GridMinus.atNode 1646,NodeMinus25.w45,CompactMinus1632.checked1645,CompactMinus1632.small1645,CompactMinus1632.nodes1645,NodeMinus25.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1632.p1646,GridMinus.atNode 1646,GridMinus.atNode 1647,NodeMinus25.w46,CompactMinus1632.checked1646,CompactMinus1632.small1646,CompactMinus1632.nodes1646,NodeMinus25.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1632.p1647,GridMinus.atNode 1647,GridMinus.atNode 1648,NodeMinus25.w47,CompactMinus1632.checked1647,CompactMinus1632.small1647,CompactMinus1632.nodes1647,NodeMinus25.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1648.p1648,GridMinus.atNode 1648,GridMinus.atNode 1649,NodeMinus25.w48,CompactMinus1648.checked1648,CompactMinus1648.small1648,CompactMinus1648.nodes1648,NodeMinus25.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1648.p1649,GridMinus.atNode 1649,GridMinus.atNode 1650,NodeMinus25.w49,CompactMinus1648.checked1649,CompactMinus1648.small1649,CompactMinus1648.nodes1649,NodeMinus25.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1648.p1650,GridMinus.atNode 1650,GridMinus.atNode 1651,NodeMinus25.w50,CompactMinus1648.checked1650,CompactMinus1648.small1650,CompactMinus1648.nodes1650,NodeMinus25.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1648.p1651,GridMinus.atNode 1651,GridMinus.atNode 1652,NodeMinus25.w51,CompactMinus1648.checked1651,CompactMinus1648.small1651,CompactMinus1648.nodes1651,NodeMinus25.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1648.p1652,GridMinus.atNode 1652,GridMinus.atNode 1653,NodeMinus25.w52,CompactMinus1648.checked1652,CompactMinus1648.small1652,CompactMinus1648.nodes1652,NodeMinus25.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1648.p1653,GridMinus.atNode 1653,GridMinus.atNode 1654,NodeMinus25.w53,CompactMinus1648.checked1653,CompactMinus1648.small1653,CompactMinus1648.nodes1653,NodeMinus25.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1648.p1654,GridMinus.atNode 1654,GridMinus.atNode 1655,NodeMinus25.w54,CompactMinus1648.checked1654,CompactMinus1648.small1654,CompactMinus1648.nodes1654,NodeMinus25.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1648.p1655,GridMinus.atNode 1655,GridMinus.atNode 1656,NodeMinus25.w55,CompactMinus1648.checked1655,CompactMinus1648.small1655,CompactMinus1648.nodes1655,NodeMinus25.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1648.p1656,GridMinus.atNode 1656,GridMinus.atNode 1657,NodeMinus25.w56,CompactMinus1648.checked1656,CompactMinus1648.small1656,CompactMinus1648.nodes1656,NodeMinus25.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1648.p1657,GridMinus.atNode 1657,GridMinus.atNode 1658,NodeMinus25.w57,CompactMinus1648.checked1657,CompactMinus1648.small1657,CompactMinus1648.nodes1657,NodeMinus25.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1648.p1658,GridMinus.atNode 1658,GridMinus.atNode 1659,NodeMinus25.w58,CompactMinus1648.checked1658,CompactMinus1648.small1658,CompactMinus1648.nodes1658,NodeMinus25.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1648.p1659,GridMinus.atNode 1659,GridMinus.atNode 1660,NodeMinus25.w59,CompactMinus1648.checked1659,CompactMinus1648.small1659,CompactMinus1648.nodes1659,NodeMinus25.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1648.p1660,GridMinus.atNode 1660,GridMinus.atNode 1661,NodeMinus25.w60,CompactMinus1648.checked1660,CompactMinus1648.small1660,CompactMinus1648.nodes1660,NodeMinus25.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1648.p1661,GridMinus.atNode 1661,GridMinus.atNode 1662,NodeMinus25.w61,CompactMinus1648.checked1661,CompactMinus1648.small1661,CompactMinus1648.nodes1661,NodeMinus25.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1648.p1662,GridMinus.atNode 1662,GridMinus.atNode 1663,NodeMinus25.w62,CompactMinus1648.checked1662,CompactMinus1648.small1662,CompactMinus1648.nodes1662,NodeMinus25.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1648.p1663,GridMinus.atNode 1663,GridMinus.atNode 1664,NodeMinus25.w63,CompactMinus1648.checked1663,CompactMinus1648.small1663,CompactMinus1648.nodes1663,NodeMinus25.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (1600+j) ∧
    (atRow j).right=GridMinus.atNode (1600+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus25
