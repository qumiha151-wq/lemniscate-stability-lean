import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus1600
import SolitonClassification.Rotating.ResetPackedPlus1616
import SolitonClassification.Rotating.ResetPackedPlus1632
import SolitonClassification.Rotating.ResetPackedPlus1648
namespace SolitonClassification.Rotating.DyadicReset.TilePlus25
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus1600.p1600,GridPlus.atNode 1600,GridPlus.atNode 1601,NodePlus25.w0,CompactPlus1600.checked1600,CompactPlus1600.small1600,CompactPlus1600.nodes1600,NodePlus25.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus1600.p1601,GridPlus.atNode 1601,GridPlus.atNode 1602,NodePlus25.w1,CompactPlus1600.checked1601,CompactPlus1600.small1601,CompactPlus1600.nodes1601,NodePlus25.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus1600.p1602,GridPlus.atNode 1602,GridPlus.atNode 1603,NodePlus25.w2,CompactPlus1600.checked1602,CompactPlus1600.small1602,CompactPlus1600.nodes1602,NodePlus25.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus1600.p1603,GridPlus.atNode 1603,GridPlus.atNode 1604,NodePlus25.w3,CompactPlus1600.checked1603,CompactPlus1600.small1603,CompactPlus1600.nodes1603,NodePlus25.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus1600.p1604,GridPlus.atNode 1604,GridPlus.atNode 1605,NodePlus25.w4,CompactPlus1600.checked1604,CompactPlus1600.small1604,CompactPlus1600.nodes1604,NodePlus25.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus1600.p1605,GridPlus.atNode 1605,GridPlus.atNode 1606,NodePlus25.w5,CompactPlus1600.checked1605,CompactPlus1600.small1605,CompactPlus1600.nodes1605,NodePlus25.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus1600.p1606,GridPlus.atNode 1606,GridPlus.atNode 1607,NodePlus25.w6,CompactPlus1600.checked1606,CompactPlus1600.small1606,CompactPlus1600.nodes1606,NodePlus25.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus1600.p1607,GridPlus.atNode 1607,GridPlus.atNode 1608,NodePlus25.w7,CompactPlus1600.checked1607,CompactPlus1600.small1607,CompactPlus1600.nodes1607,NodePlus25.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus1600.p1608,GridPlus.atNode 1608,GridPlus.atNode 1609,NodePlus25.w8,CompactPlus1600.checked1608,CompactPlus1600.small1608,CompactPlus1600.nodes1608,NodePlus25.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus1600.p1609,GridPlus.atNode 1609,GridPlus.atNode 1610,NodePlus25.w9,CompactPlus1600.checked1609,CompactPlus1600.small1609,CompactPlus1600.nodes1609,NodePlus25.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus1600.p1610,GridPlus.atNode 1610,GridPlus.atNode 1611,NodePlus25.w10,CompactPlus1600.checked1610,CompactPlus1600.small1610,CompactPlus1600.nodes1610,NodePlus25.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus1600.p1611,GridPlus.atNode 1611,GridPlus.atNode 1612,NodePlus25.w11,CompactPlus1600.checked1611,CompactPlus1600.small1611,CompactPlus1600.nodes1611,NodePlus25.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus1600.p1612,GridPlus.atNode 1612,GridPlus.atNode 1613,NodePlus25.w12,CompactPlus1600.checked1612,CompactPlus1600.small1612,CompactPlus1600.nodes1612,NodePlus25.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus1600.p1613,GridPlus.atNode 1613,GridPlus.atNode 1614,NodePlus25.w13,CompactPlus1600.checked1613,CompactPlus1600.small1613,CompactPlus1600.nodes1613,NodePlus25.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus1600.p1614,GridPlus.atNode 1614,GridPlus.atNode 1615,NodePlus25.w14,CompactPlus1600.checked1614,CompactPlus1600.small1614,CompactPlus1600.nodes1614,NodePlus25.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus1600.p1615,GridPlus.atNode 1615,GridPlus.atNode 1616,NodePlus25.w15,CompactPlus1600.checked1615,CompactPlus1600.small1615,CompactPlus1600.nodes1615,NodePlus25.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus1616.p1616,GridPlus.atNode 1616,GridPlus.atNode 1617,NodePlus25.w16,CompactPlus1616.checked1616,CompactPlus1616.small1616,CompactPlus1616.nodes1616,NodePlus25.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus1616.p1617,GridPlus.atNode 1617,GridPlus.atNode 1618,NodePlus25.w17,CompactPlus1616.checked1617,CompactPlus1616.small1617,CompactPlus1616.nodes1617,NodePlus25.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus1616.p1618,GridPlus.atNode 1618,GridPlus.atNode 1619,NodePlus25.w18,CompactPlus1616.checked1618,CompactPlus1616.small1618,CompactPlus1616.nodes1618,NodePlus25.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus1616.p1619,GridPlus.atNode 1619,GridPlus.atNode 1620,NodePlus25.w19,CompactPlus1616.checked1619,CompactPlus1616.small1619,CompactPlus1616.nodes1619,NodePlus25.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus1616.p1620,GridPlus.atNode 1620,GridPlus.atNode 1621,NodePlus25.w20,CompactPlus1616.checked1620,CompactPlus1616.small1620,CompactPlus1616.nodes1620,NodePlus25.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus1616.p1621,GridPlus.atNode 1621,GridPlus.atNode 1622,NodePlus25.w21,CompactPlus1616.checked1621,CompactPlus1616.small1621,CompactPlus1616.nodes1621,NodePlus25.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus1616.p1622,GridPlus.atNode 1622,GridPlus.atNode 1623,NodePlus25.w22,CompactPlus1616.checked1622,CompactPlus1616.small1622,CompactPlus1616.nodes1622,NodePlus25.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus1616.p1623,GridPlus.atNode 1623,GridPlus.atNode 1624,NodePlus25.w23,CompactPlus1616.checked1623,CompactPlus1616.small1623,CompactPlus1616.nodes1623,NodePlus25.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus1616.p1624,GridPlus.atNode 1624,GridPlus.atNode 1625,NodePlus25.w24,CompactPlus1616.checked1624,CompactPlus1616.small1624,CompactPlus1616.nodes1624,NodePlus25.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus1616.p1625,GridPlus.atNode 1625,GridPlus.atNode 1626,NodePlus25.w25,CompactPlus1616.checked1625,CompactPlus1616.small1625,CompactPlus1616.nodes1625,NodePlus25.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus1616.p1626,GridPlus.atNode 1626,GridPlus.atNode 1627,NodePlus25.w26,CompactPlus1616.checked1626,CompactPlus1616.small1626,CompactPlus1616.nodes1626,NodePlus25.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus1616.p1627,GridPlus.atNode 1627,GridPlus.atNode 1628,NodePlus25.w27,CompactPlus1616.checked1627,CompactPlus1616.small1627,CompactPlus1616.nodes1627,NodePlus25.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus1616.p1628,GridPlus.atNode 1628,GridPlus.atNode 1629,NodePlus25.w28,CompactPlus1616.checked1628,CompactPlus1616.small1628,CompactPlus1616.nodes1628,NodePlus25.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus1616.p1629,GridPlus.atNode 1629,GridPlus.atNode 1630,NodePlus25.w29,CompactPlus1616.checked1629,CompactPlus1616.small1629,CompactPlus1616.nodes1629,NodePlus25.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus1616.p1630,GridPlus.atNode 1630,GridPlus.atNode 1631,NodePlus25.w30,CompactPlus1616.checked1630,CompactPlus1616.small1630,CompactPlus1616.nodes1630,NodePlus25.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus1616.p1631,GridPlus.atNode 1631,GridPlus.atNode 1632,NodePlus25.w31,CompactPlus1616.checked1631,CompactPlus1616.small1631,CompactPlus1616.nodes1631,NodePlus25.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus1632.p1632,GridPlus.atNode 1632,GridPlus.atNode 1633,NodePlus25.w32,CompactPlus1632.checked1632,CompactPlus1632.small1632,CompactPlus1632.nodes1632,NodePlus25.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus1632.p1633,GridPlus.atNode 1633,GridPlus.atNode 1634,NodePlus25.w33,CompactPlus1632.checked1633,CompactPlus1632.small1633,CompactPlus1632.nodes1633,NodePlus25.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus1632.p1634,GridPlus.atNode 1634,GridPlus.atNode 1635,NodePlus25.w34,CompactPlus1632.checked1634,CompactPlus1632.small1634,CompactPlus1632.nodes1634,NodePlus25.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus1632.p1635,GridPlus.atNode 1635,GridPlus.atNode 1636,NodePlus25.w35,CompactPlus1632.checked1635,CompactPlus1632.small1635,CompactPlus1632.nodes1635,NodePlus25.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus1632.p1636,GridPlus.atNode 1636,GridPlus.atNode 1637,NodePlus25.w36,CompactPlus1632.checked1636,CompactPlus1632.small1636,CompactPlus1632.nodes1636,NodePlus25.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus1632.p1637,GridPlus.atNode 1637,GridPlus.atNode 1638,NodePlus25.w37,CompactPlus1632.checked1637,CompactPlus1632.small1637,CompactPlus1632.nodes1637,NodePlus25.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus1632.p1638,GridPlus.atNode 1638,GridPlus.atNode 1639,NodePlus25.w38,CompactPlus1632.checked1638,CompactPlus1632.small1638,CompactPlus1632.nodes1638,NodePlus25.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus1632.p1639,GridPlus.atNode 1639,GridPlus.atNode 1640,NodePlus25.w39,CompactPlus1632.checked1639,CompactPlus1632.small1639,CompactPlus1632.nodes1639,NodePlus25.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus1632.p1640,GridPlus.atNode 1640,GridPlus.atNode 1641,NodePlus25.w40,CompactPlus1632.checked1640,CompactPlus1632.small1640,CompactPlus1632.nodes1640,NodePlus25.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus1632.p1641,GridPlus.atNode 1641,GridPlus.atNode 1642,NodePlus25.w41,CompactPlus1632.checked1641,CompactPlus1632.small1641,CompactPlus1632.nodes1641,NodePlus25.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus1632.p1642,GridPlus.atNode 1642,GridPlus.atNode 1643,NodePlus25.w42,CompactPlus1632.checked1642,CompactPlus1632.small1642,CompactPlus1632.nodes1642,NodePlus25.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus1632.p1643,GridPlus.atNode 1643,GridPlus.atNode 1644,NodePlus25.w43,CompactPlus1632.checked1643,CompactPlus1632.small1643,CompactPlus1632.nodes1643,NodePlus25.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus1632.p1644,GridPlus.atNode 1644,GridPlus.atNode 1645,NodePlus25.w44,CompactPlus1632.checked1644,CompactPlus1632.small1644,CompactPlus1632.nodes1644,NodePlus25.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus1632.p1645,GridPlus.atNode 1645,GridPlus.atNode 1646,NodePlus25.w45,CompactPlus1632.checked1645,CompactPlus1632.small1645,CompactPlus1632.nodes1645,NodePlus25.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus1632.p1646,GridPlus.atNode 1646,GridPlus.atNode 1647,NodePlus25.w46,CompactPlus1632.checked1646,CompactPlus1632.small1646,CompactPlus1632.nodes1646,NodePlus25.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus1632.p1647,GridPlus.atNode 1647,GridPlus.atNode 1648,NodePlus25.w47,CompactPlus1632.checked1647,CompactPlus1632.small1647,CompactPlus1632.nodes1647,NodePlus25.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus1648.p1648,GridPlus.atNode 1648,GridPlus.atNode 1649,NodePlus25.w48,CompactPlus1648.checked1648,CompactPlus1648.small1648,CompactPlus1648.nodes1648,NodePlus25.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus1648.p1649,GridPlus.atNode 1649,GridPlus.atNode 1650,NodePlus25.w49,CompactPlus1648.checked1649,CompactPlus1648.small1649,CompactPlus1648.nodes1649,NodePlus25.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus1648.p1650,GridPlus.atNode 1650,GridPlus.atNode 1651,NodePlus25.w50,CompactPlus1648.checked1650,CompactPlus1648.small1650,CompactPlus1648.nodes1650,NodePlus25.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus1648.p1651,GridPlus.atNode 1651,GridPlus.atNode 1652,NodePlus25.w51,CompactPlus1648.checked1651,CompactPlus1648.small1651,CompactPlus1648.nodes1651,NodePlus25.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus1648.p1652,GridPlus.atNode 1652,GridPlus.atNode 1653,NodePlus25.w52,CompactPlus1648.checked1652,CompactPlus1648.small1652,CompactPlus1648.nodes1652,NodePlus25.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus1648.p1653,GridPlus.atNode 1653,GridPlus.atNode 1654,NodePlus25.w53,CompactPlus1648.checked1653,CompactPlus1648.small1653,CompactPlus1648.nodes1653,NodePlus25.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus1648.p1654,GridPlus.atNode 1654,GridPlus.atNode 1655,NodePlus25.w54,CompactPlus1648.checked1654,CompactPlus1648.small1654,CompactPlus1648.nodes1654,NodePlus25.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus1648.p1655,GridPlus.atNode 1655,GridPlus.atNode 1656,NodePlus25.w55,CompactPlus1648.checked1655,CompactPlus1648.small1655,CompactPlus1648.nodes1655,NodePlus25.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus1648.p1656,GridPlus.atNode 1656,GridPlus.atNode 1657,NodePlus25.w56,CompactPlus1648.checked1656,CompactPlus1648.small1656,CompactPlus1648.nodes1656,NodePlus25.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus1648.p1657,GridPlus.atNode 1657,GridPlus.atNode 1658,NodePlus25.w57,CompactPlus1648.checked1657,CompactPlus1648.small1657,CompactPlus1648.nodes1657,NodePlus25.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus1648.p1658,GridPlus.atNode 1658,GridPlus.atNode 1659,NodePlus25.w58,CompactPlus1648.checked1658,CompactPlus1648.small1658,CompactPlus1648.nodes1658,NodePlus25.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus1648.p1659,GridPlus.atNode 1659,GridPlus.atNode 1660,NodePlus25.w59,CompactPlus1648.checked1659,CompactPlus1648.small1659,CompactPlus1648.nodes1659,NodePlus25.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus1648.p1660,GridPlus.atNode 1660,GridPlus.atNode 1661,NodePlus25.w60,CompactPlus1648.checked1660,CompactPlus1648.small1660,CompactPlus1648.nodes1660,NodePlus25.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus1648.p1661,GridPlus.atNode 1661,GridPlus.atNode 1662,NodePlus25.w61,CompactPlus1648.checked1661,CompactPlus1648.small1661,CompactPlus1648.nodes1661,NodePlus25.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus1648.p1662,GridPlus.atNode 1662,GridPlus.atNode 1663,NodePlus25.w62,CompactPlus1648.checked1662,CompactPlus1648.small1662,CompactPlus1648.nodes1662,NodePlus25.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus1648.p1663,GridPlus.atNode 1663,GridPlus.atNode 1664,NodePlus25.w63,CompactPlus1648.checked1663,CompactPlus1648.small1663,CompactPlus1648.nodes1663,NodePlus25.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (1600+j) ∧
    (atRow j).right=GridPlus.atNode (1600+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus25
