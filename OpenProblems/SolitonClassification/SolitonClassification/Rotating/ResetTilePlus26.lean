import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus1664
import SolitonClassification.Rotating.ResetPackedPlus1680
import SolitonClassification.Rotating.ResetPackedPlus1696
import SolitonClassification.Rotating.ResetPackedPlus1712
namespace SolitonClassification.Rotating.DyadicReset.TilePlus26
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus1664.p1664,GridPlus.atNode 1664,GridPlus.atNode 1665,NodePlus26.w0,CompactPlus1664.checked1664,CompactPlus1664.small1664,CompactPlus1664.nodes1664,NodePlus26.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus1664.p1665,GridPlus.atNode 1665,GridPlus.atNode 1666,NodePlus26.w1,CompactPlus1664.checked1665,CompactPlus1664.small1665,CompactPlus1664.nodes1665,NodePlus26.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus1664.p1666,GridPlus.atNode 1666,GridPlus.atNode 1667,NodePlus26.w2,CompactPlus1664.checked1666,CompactPlus1664.small1666,CompactPlus1664.nodes1666,NodePlus26.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus1664.p1667,GridPlus.atNode 1667,GridPlus.atNode 1668,NodePlus26.w3,CompactPlus1664.checked1667,CompactPlus1664.small1667,CompactPlus1664.nodes1667,NodePlus26.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus1664.p1668,GridPlus.atNode 1668,GridPlus.atNode 1669,NodePlus26.w4,CompactPlus1664.checked1668,CompactPlus1664.small1668,CompactPlus1664.nodes1668,NodePlus26.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus1664.p1669,GridPlus.atNode 1669,GridPlus.atNode 1670,NodePlus26.w5,CompactPlus1664.checked1669,CompactPlus1664.small1669,CompactPlus1664.nodes1669,NodePlus26.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus1664.p1670,GridPlus.atNode 1670,GridPlus.atNode 1671,NodePlus26.w6,CompactPlus1664.checked1670,CompactPlus1664.small1670,CompactPlus1664.nodes1670,NodePlus26.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus1664.p1671,GridPlus.atNode 1671,GridPlus.atNode 1672,NodePlus26.w7,CompactPlus1664.checked1671,CompactPlus1664.small1671,CompactPlus1664.nodes1671,NodePlus26.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus1664.p1672,GridPlus.atNode 1672,GridPlus.atNode 1673,NodePlus26.w8,CompactPlus1664.checked1672,CompactPlus1664.small1672,CompactPlus1664.nodes1672,NodePlus26.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus1664.p1673,GridPlus.atNode 1673,GridPlus.atNode 1674,NodePlus26.w9,CompactPlus1664.checked1673,CompactPlus1664.small1673,CompactPlus1664.nodes1673,NodePlus26.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus1664.p1674,GridPlus.atNode 1674,GridPlus.atNode 1675,NodePlus26.w10,CompactPlus1664.checked1674,CompactPlus1664.small1674,CompactPlus1664.nodes1674,NodePlus26.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus1664.p1675,GridPlus.atNode 1675,GridPlus.atNode 1676,NodePlus26.w11,CompactPlus1664.checked1675,CompactPlus1664.small1675,CompactPlus1664.nodes1675,NodePlus26.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus1664.p1676,GridPlus.atNode 1676,GridPlus.atNode 1677,NodePlus26.w12,CompactPlus1664.checked1676,CompactPlus1664.small1676,CompactPlus1664.nodes1676,NodePlus26.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus1664.p1677,GridPlus.atNode 1677,GridPlus.atNode 1678,NodePlus26.w13,CompactPlus1664.checked1677,CompactPlus1664.small1677,CompactPlus1664.nodes1677,NodePlus26.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus1664.p1678,GridPlus.atNode 1678,GridPlus.atNode 1679,NodePlus26.w14,CompactPlus1664.checked1678,CompactPlus1664.small1678,CompactPlus1664.nodes1678,NodePlus26.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus1664.p1679,GridPlus.atNode 1679,GridPlus.atNode 1680,NodePlus26.w15,CompactPlus1664.checked1679,CompactPlus1664.small1679,CompactPlus1664.nodes1679,NodePlus26.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus1680.p1680,GridPlus.atNode 1680,GridPlus.atNode 1681,NodePlus26.w16,CompactPlus1680.checked1680,CompactPlus1680.small1680,CompactPlus1680.nodes1680,NodePlus26.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus1680.p1681,GridPlus.atNode 1681,GridPlus.atNode 1682,NodePlus26.w17,CompactPlus1680.checked1681,CompactPlus1680.small1681,CompactPlus1680.nodes1681,NodePlus26.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus1680.p1682,GridPlus.atNode 1682,GridPlus.atNode 1683,NodePlus26.w18,CompactPlus1680.checked1682,CompactPlus1680.small1682,CompactPlus1680.nodes1682,NodePlus26.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus1680.p1683,GridPlus.atNode 1683,GridPlus.atNode 1684,NodePlus26.w19,CompactPlus1680.checked1683,CompactPlus1680.small1683,CompactPlus1680.nodes1683,NodePlus26.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus1680.p1684,GridPlus.atNode 1684,GridPlus.atNode 1685,NodePlus26.w20,CompactPlus1680.checked1684,CompactPlus1680.small1684,CompactPlus1680.nodes1684,NodePlus26.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus1680.p1685,GridPlus.atNode 1685,GridPlus.atNode 1686,NodePlus26.w21,CompactPlus1680.checked1685,CompactPlus1680.small1685,CompactPlus1680.nodes1685,NodePlus26.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus1680.p1686,GridPlus.atNode 1686,GridPlus.atNode 1687,NodePlus26.w22,CompactPlus1680.checked1686,CompactPlus1680.small1686,CompactPlus1680.nodes1686,NodePlus26.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus1680.p1687,GridPlus.atNode 1687,GridPlus.atNode 1688,NodePlus26.w23,CompactPlus1680.checked1687,CompactPlus1680.small1687,CompactPlus1680.nodes1687,NodePlus26.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus1680.p1688,GridPlus.atNode 1688,GridPlus.atNode 1689,NodePlus26.w24,CompactPlus1680.checked1688,CompactPlus1680.small1688,CompactPlus1680.nodes1688,NodePlus26.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus1680.p1689,GridPlus.atNode 1689,GridPlus.atNode 1690,NodePlus26.w25,CompactPlus1680.checked1689,CompactPlus1680.small1689,CompactPlus1680.nodes1689,NodePlus26.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus1680.p1690,GridPlus.atNode 1690,GridPlus.atNode 1691,NodePlus26.w26,CompactPlus1680.checked1690,CompactPlus1680.small1690,CompactPlus1680.nodes1690,NodePlus26.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus1680.p1691,GridPlus.atNode 1691,GridPlus.atNode 1692,NodePlus26.w27,CompactPlus1680.checked1691,CompactPlus1680.small1691,CompactPlus1680.nodes1691,NodePlus26.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus1680.p1692,GridPlus.atNode 1692,GridPlus.atNode 1693,NodePlus26.w28,CompactPlus1680.checked1692,CompactPlus1680.small1692,CompactPlus1680.nodes1692,NodePlus26.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus1680.p1693,GridPlus.atNode 1693,GridPlus.atNode 1694,NodePlus26.w29,CompactPlus1680.checked1693,CompactPlus1680.small1693,CompactPlus1680.nodes1693,NodePlus26.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus1680.p1694,GridPlus.atNode 1694,GridPlus.atNode 1695,NodePlus26.w30,CompactPlus1680.checked1694,CompactPlus1680.small1694,CompactPlus1680.nodes1694,NodePlus26.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus1680.p1695,GridPlus.atNode 1695,GridPlus.atNode 1696,NodePlus26.w31,CompactPlus1680.checked1695,CompactPlus1680.small1695,CompactPlus1680.nodes1695,NodePlus26.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus1696.p1696,GridPlus.atNode 1696,GridPlus.atNode 1697,NodePlus26.w32,CompactPlus1696.checked1696,CompactPlus1696.small1696,CompactPlus1696.nodes1696,NodePlus26.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus1696.p1697,GridPlus.atNode 1697,GridPlus.atNode 1698,NodePlus26.w33,CompactPlus1696.checked1697,CompactPlus1696.small1697,CompactPlus1696.nodes1697,NodePlus26.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus1696.p1698,GridPlus.atNode 1698,GridPlus.atNode 1699,NodePlus26.w34,CompactPlus1696.checked1698,CompactPlus1696.small1698,CompactPlus1696.nodes1698,NodePlus26.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus1696.p1699,GridPlus.atNode 1699,GridPlus.atNode 1700,NodePlus26.w35,CompactPlus1696.checked1699,CompactPlus1696.small1699,CompactPlus1696.nodes1699,NodePlus26.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus1696.p1700,GridPlus.atNode 1700,GridPlus.atNode 1701,NodePlus26.w36,CompactPlus1696.checked1700,CompactPlus1696.small1700,CompactPlus1696.nodes1700,NodePlus26.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus1696.p1701,GridPlus.atNode 1701,GridPlus.atNode 1702,NodePlus26.w37,CompactPlus1696.checked1701,CompactPlus1696.small1701,CompactPlus1696.nodes1701,NodePlus26.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus1696.p1702,GridPlus.atNode 1702,GridPlus.atNode 1703,NodePlus26.w38,CompactPlus1696.checked1702,CompactPlus1696.small1702,CompactPlus1696.nodes1702,NodePlus26.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus1696.p1703,GridPlus.atNode 1703,GridPlus.atNode 1704,NodePlus26.w39,CompactPlus1696.checked1703,CompactPlus1696.small1703,CompactPlus1696.nodes1703,NodePlus26.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus1696.p1704,GridPlus.atNode 1704,GridPlus.atNode 1705,NodePlus26.w40,CompactPlus1696.checked1704,CompactPlus1696.small1704,CompactPlus1696.nodes1704,NodePlus26.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus1696.p1705,GridPlus.atNode 1705,GridPlus.atNode 1706,NodePlus26.w41,CompactPlus1696.checked1705,CompactPlus1696.small1705,CompactPlus1696.nodes1705,NodePlus26.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus1696.p1706,GridPlus.atNode 1706,GridPlus.atNode 1707,NodePlus26.w42,CompactPlus1696.checked1706,CompactPlus1696.small1706,CompactPlus1696.nodes1706,NodePlus26.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus1696.p1707,GridPlus.atNode 1707,GridPlus.atNode 1708,NodePlus26.w43,CompactPlus1696.checked1707,CompactPlus1696.small1707,CompactPlus1696.nodes1707,NodePlus26.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus1696.p1708,GridPlus.atNode 1708,GridPlus.atNode 1709,NodePlus26.w44,CompactPlus1696.checked1708,CompactPlus1696.small1708,CompactPlus1696.nodes1708,NodePlus26.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus1696.p1709,GridPlus.atNode 1709,GridPlus.atNode 1710,NodePlus26.w45,CompactPlus1696.checked1709,CompactPlus1696.small1709,CompactPlus1696.nodes1709,NodePlus26.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus1696.p1710,GridPlus.atNode 1710,GridPlus.atNode 1711,NodePlus26.w46,CompactPlus1696.checked1710,CompactPlus1696.small1710,CompactPlus1696.nodes1710,NodePlus26.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus1696.p1711,GridPlus.atNode 1711,GridPlus.atNode 1712,NodePlus26.w47,CompactPlus1696.checked1711,CompactPlus1696.small1711,CompactPlus1696.nodes1711,NodePlus26.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus1712.p1712,GridPlus.atNode 1712,GridPlus.atNode 1713,NodePlus26.w48,CompactPlus1712.checked1712,CompactPlus1712.small1712,CompactPlus1712.nodes1712,NodePlus26.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus1712.p1713,GridPlus.atNode 1713,GridPlus.atNode 1714,NodePlus26.w49,CompactPlus1712.checked1713,CompactPlus1712.small1713,CompactPlus1712.nodes1713,NodePlus26.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus1712.p1714,GridPlus.atNode 1714,GridPlus.atNode 1715,NodePlus26.w50,CompactPlus1712.checked1714,CompactPlus1712.small1714,CompactPlus1712.nodes1714,NodePlus26.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus1712.p1715,GridPlus.atNode 1715,GridPlus.atNode 1716,NodePlus26.w51,CompactPlus1712.checked1715,CompactPlus1712.small1715,CompactPlus1712.nodes1715,NodePlus26.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus1712.p1716,GridPlus.atNode 1716,GridPlus.atNode 1717,NodePlus26.w52,CompactPlus1712.checked1716,CompactPlus1712.small1716,CompactPlus1712.nodes1716,NodePlus26.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus1712.p1717,GridPlus.atNode 1717,GridPlus.atNode 1718,NodePlus26.w53,CompactPlus1712.checked1717,CompactPlus1712.small1717,CompactPlus1712.nodes1717,NodePlus26.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus1712.p1718,GridPlus.atNode 1718,GridPlus.atNode 1719,NodePlus26.w54,CompactPlus1712.checked1718,CompactPlus1712.small1718,CompactPlus1712.nodes1718,NodePlus26.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus1712.p1719,GridPlus.atNode 1719,GridPlus.atNode 1720,NodePlus26.w55,CompactPlus1712.checked1719,CompactPlus1712.small1719,CompactPlus1712.nodes1719,NodePlus26.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus1712.p1720,GridPlus.atNode 1720,GridPlus.atNode 1721,NodePlus26.w56,CompactPlus1712.checked1720,CompactPlus1712.small1720,CompactPlus1712.nodes1720,NodePlus26.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus1712.p1721,GridPlus.atNode 1721,GridPlus.atNode 1722,NodePlus26.w57,CompactPlus1712.checked1721,CompactPlus1712.small1721,CompactPlus1712.nodes1721,NodePlus26.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus1712.p1722,GridPlus.atNode 1722,GridPlus.atNode 1723,NodePlus26.w58,CompactPlus1712.checked1722,CompactPlus1712.small1722,CompactPlus1712.nodes1722,NodePlus26.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus1712.p1723,GridPlus.atNode 1723,GridPlus.atNode 1724,NodePlus26.w59,CompactPlus1712.checked1723,CompactPlus1712.small1723,CompactPlus1712.nodes1723,NodePlus26.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus1712.p1724,GridPlus.atNode 1724,GridPlus.atNode 1725,NodePlus26.w60,CompactPlus1712.checked1724,CompactPlus1712.small1724,CompactPlus1712.nodes1724,NodePlus26.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus1712.p1725,GridPlus.atNode 1725,GridPlus.atNode 1726,NodePlus26.w61,CompactPlus1712.checked1725,CompactPlus1712.small1725,CompactPlus1712.nodes1725,NodePlus26.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus1712.p1726,GridPlus.atNode 1726,GridPlus.atNode 1727,NodePlus26.w62,CompactPlus1712.checked1726,CompactPlus1712.small1726,CompactPlus1712.nodes1726,NodePlus26.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus1712.p1727,GridPlus.atNode 1727,GridPlus.atNode 1728,NodePlus26.w63,CompactPlus1712.checked1727,CompactPlus1712.small1727,CompactPlus1712.nodes1727,NodePlus26.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (1664+j) ∧
    (atRow j).right=GridPlus.atNode (1664+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus26
