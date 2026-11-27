import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus1664
import SolitonClassification.Rotating.ResetPackedMinus1680
import SolitonClassification.Rotating.ResetPackedMinus1696
import SolitonClassification.Rotating.ResetPackedMinus1712
namespace SolitonClassification.Rotating.DyadicReset.TileMinus26
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1664.p1664,GridMinus.atNode 1664,GridMinus.atNode 1665,NodeMinus26.w0,CompactMinus1664.checked1664,CompactMinus1664.small1664,CompactMinus1664.nodes1664,NodeMinus26.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1664.p1665,GridMinus.atNode 1665,GridMinus.atNode 1666,NodeMinus26.w1,CompactMinus1664.checked1665,CompactMinus1664.small1665,CompactMinus1664.nodes1665,NodeMinus26.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1664.p1666,GridMinus.atNode 1666,GridMinus.atNode 1667,NodeMinus26.w2,CompactMinus1664.checked1666,CompactMinus1664.small1666,CompactMinus1664.nodes1666,NodeMinus26.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1664.p1667,GridMinus.atNode 1667,GridMinus.atNode 1668,NodeMinus26.w3,CompactMinus1664.checked1667,CompactMinus1664.small1667,CompactMinus1664.nodes1667,NodeMinus26.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1664.p1668,GridMinus.atNode 1668,GridMinus.atNode 1669,NodeMinus26.w4,CompactMinus1664.checked1668,CompactMinus1664.small1668,CompactMinus1664.nodes1668,NodeMinus26.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1664.p1669,GridMinus.atNode 1669,GridMinus.atNode 1670,NodeMinus26.w5,CompactMinus1664.checked1669,CompactMinus1664.small1669,CompactMinus1664.nodes1669,NodeMinus26.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1664.p1670,GridMinus.atNode 1670,GridMinus.atNode 1671,NodeMinus26.w6,CompactMinus1664.checked1670,CompactMinus1664.small1670,CompactMinus1664.nodes1670,NodeMinus26.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1664.p1671,GridMinus.atNode 1671,GridMinus.atNode 1672,NodeMinus26.w7,CompactMinus1664.checked1671,CompactMinus1664.small1671,CompactMinus1664.nodes1671,NodeMinus26.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1664.p1672,GridMinus.atNode 1672,GridMinus.atNode 1673,NodeMinus26.w8,CompactMinus1664.checked1672,CompactMinus1664.small1672,CompactMinus1664.nodes1672,NodeMinus26.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1664.p1673,GridMinus.atNode 1673,GridMinus.atNode 1674,NodeMinus26.w9,CompactMinus1664.checked1673,CompactMinus1664.small1673,CompactMinus1664.nodes1673,NodeMinus26.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1664.p1674,GridMinus.atNode 1674,GridMinus.atNode 1675,NodeMinus26.w10,CompactMinus1664.checked1674,CompactMinus1664.small1674,CompactMinus1664.nodes1674,NodeMinus26.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1664.p1675,GridMinus.atNode 1675,GridMinus.atNode 1676,NodeMinus26.w11,CompactMinus1664.checked1675,CompactMinus1664.small1675,CompactMinus1664.nodes1675,NodeMinus26.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1664.p1676,GridMinus.atNode 1676,GridMinus.atNode 1677,NodeMinus26.w12,CompactMinus1664.checked1676,CompactMinus1664.small1676,CompactMinus1664.nodes1676,NodeMinus26.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1664.p1677,GridMinus.atNode 1677,GridMinus.atNode 1678,NodeMinus26.w13,CompactMinus1664.checked1677,CompactMinus1664.small1677,CompactMinus1664.nodes1677,NodeMinus26.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1664.p1678,GridMinus.atNode 1678,GridMinus.atNode 1679,NodeMinus26.w14,CompactMinus1664.checked1678,CompactMinus1664.small1678,CompactMinus1664.nodes1678,NodeMinus26.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1664.p1679,GridMinus.atNode 1679,GridMinus.atNode 1680,NodeMinus26.w15,CompactMinus1664.checked1679,CompactMinus1664.small1679,CompactMinus1664.nodes1679,NodeMinus26.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1680.p1680,GridMinus.atNode 1680,GridMinus.atNode 1681,NodeMinus26.w16,CompactMinus1680.checked1680,CompactMinus1680.small1680,CompactMinus1680.nodes1680,NodeMinus26.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1680.p1681,GridMinus.atNode 1681,GridMinus.atNode 1682,NodeMinus26.w17,CompactMinus1680.checked1681,CompactMinus1680.small1681,CompactMinus1680.nodes1681,NodeMinus26.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1680.p1682,GridMinus.atNode 1682,GridMinus.atNode 1683,NodeMinus26.w18,CompactMinus1680.checked1682,CompactMinus1680.small1682,CompactMinus1680.nodes1682,NodeMinus26.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1680.p1683,GridMinus.atNode 1683,GridMinus.atNode 1684,NodeMinus26.w19,CompactMinus1680.checked1683,CompactMinus1680.small1683,CompactMinus1680.nodes1683,NodeMinus26.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1680.p1684,GridMinus.atNode 1684,GridMinus.atNode 1685,NodeMinus26.w20,CompactMinus1680.checked1684,CompactMinus1680.small1684,CompactMinus1680.nodes1684,NodeMinus26.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1680.p1685,GridMinus.atNode 1685,GridMinus.atNode 1686,NodeMinus26.w21,CompactMinus1680.checked1685,CompactMinus1680.small1685,CompactMinus1680.nodes1685,NodeMinus26.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1680.p1686,GridMinus.atNode 1686,GridMinus.atNode 1687,NodeMinus26.w22,CompactMinus1680.checked1686,CompactMinus1680.small1686,CompactMinus1680.nodes1686,NodeMinus26.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1680.p1687,GridMinus.atNode 1687,GridMinus.atNode 1688,NodeMinus26.w23,CompactMinus1680.checked1687,CompactMinus1680.small1687,CompactMinus1680.nodes1687,NodeMinus26.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1680.p1688,GridMinus.atNode 1688,GridMinus.atNode 1689,NodeMinus26.w24,CompactMinus1680.checked1688,CompactMinus1680.small1688,CompactMinus1680.nodes1688,NodeMinus26.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1680.p1689,GridMinus.atNode 1689,GridMinus.atNode 1690,NodeMinus26.w25,CompactMinus1680.checked1689,CompactMinus1680.small1689,CompactMinus1680.nodes1689,NodeMinus26.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1680.p1690,GridMinus.atNode 1690,GridMinus.atNode 1691,NodeMinus26.w26,CompactMinus1680.checked1690,CompactMinus1680.small1690,CompactMinus1680.nodes1690,NodeMinus26.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1680.p1691,GridMinus.atNode 1691,GridMinus.atNode 1692,NodeMinus26.w27,CompactMinus1680.checked1691,CompactMinus1680.small1691,CompactMinus1680.nodes1691,NodeMinus26.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1680.p1692,GridMinus.atNode 1692,GridMinus.atNode 1693,NodeMinus26.w28,CompactMinus1680.checked1692,CompactMinus1680.small1692,CompactMinus1680.nodes1692,NodeMinus26.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1680.p1693,GridMinus.atNode 1693,GridMinus.atNode 1694,NodeMinus26.w29,CompactMinus1680.checked1693,CompactMinus1680.small1693,CompactMinus1680.nodes1693,NodeMinus26.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1680.p1694,GridMinus.atNode 1694,GridMinus.atNode 1695,NodeMinus26.w30,CompactMinus1680.checked1694,CompactMinus1680.small1694,CompactMinus1680.nodes1694,NodeMinus26.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1680.p1695,GridMinus.atNode 1695,GridMinus.atNode 1696,NodeMinus26.w31,CompactMinus1680.checked1695,CompactMinus1680.small1695,CompactMinus1680.nodes1695,NodeMinus26.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1696.p1696,GridMinus.atNode 1696,GridMinus.atNode 1697,NodeMinus26.w32,CompactMinus1696.checked1696,CompactMinus1696.small1696,CompactMinus1696.nodes1696,NodeMinus26.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1696.p1697,GridMinus.atNode 1697,GridMinus.atNode 1698,NodeMinus26.w33,CompactMinus1696.checked1697,CompactMinus1696.small1697,CompactMinus1696.nodes1697,NodeMinus26.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1696.p1698,GridMinus.atNode 1698,GridMinus.atNode 1699,NodeMinus26.w34,CompactMinus1696.checked1698,CompactMinus1696.small1698,CompactMinus1696.nodes1698,NodeMinus26.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1696.p1699,GridMinus.atNode 1699,GridMinus.atNode 1700,NodeMinus26.w35,CompactMinus1696.checked1699,CompactMinus1696.small1699,CompactMinus1696.nodes1699,NodeMinus26.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1696.p1700,GridMinus.atNode 1700,GridMinus.atNode 1701,NodeMinus26.w36,CompactMinus1696.checked1700,CompactMinus1696.small1700,CompactMinus1696.nodes1700,NodeMinus26.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1696.p1701,GridMinus.atNode 1701,GridMinus.atNode 1702,NodeMinus26.w37,CompactMinus1696.checked1701,CompactMinus1696.small1701,CompactMinus1696.nodes1701,NodeMinus26.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1696.p1702,GridMinus.atNode 1702,GridMinus.atNode 1703,NodeMinus26.w38,CompactMinus1696.checked1702,CompactMinus1696.small1702,CompactMinus1696.nodes1702,NodeMinus26.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1696.p1703,GridMinus.atNode 1703,GridMinus.atNode 1704,NodeMinus26.w39,CompactMinus1696.checked1703,CompactMinus1696.small1703,CompactMinus1696.nodes1703,NodeMinus26.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1696.p1704,GridMinus.atNode 1704,GridMinus.atNode 1705,NodeMinus26.w40,CompactMinus1696.checked1704,CompactMinus1696.small1704,CompactMinus1696.nodes1704,NodeMinus26.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1696.p1705,GridMinus.atNode 1705,GridMinus.atNode 1706,NodeMinus26.w41,CompactMinus1696.checked1705,CompactMinus1696.small1705,CompactMinus1696.nodes1705,NodeMinus26.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1696.p1706,GridMinus.atNode 1706,GridMinus.atNode 1707,NodeMinus26.w42,CompactMinus1696.checked1706,CompactMinus1696.small1706,CompactMinus1696.nodes1706,NodeMinus26.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1696.p1707,GridMinus.atNode 1707,GridMinus.atNode 1708,NodeMinus26.w43,CompactMinus1696.checked1707,CompactMinus1696.small1707,CompactMinus1696.nodes1707,NodeMinus26.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1696.p1708,GridMinus.atNode 1708,GridMinus.atNode 1709,NodeMinus26.w44,CompactMinus1696.checked1708,CompactMinus1696.small1708,CompactMinus1696.nodes1708,NodeMinus26.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1696.p1709,GridMinus.atNode 1709,GridMinus.atNode 1710,NodeMinus26.w45,CompactMinus1696.checked1709,CompactMinus1696.small1709,CompactMinus1696.nodes1709,NodeMinus26.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1696.p1710,GridMinus.atNode 1710,GridMinus.atNode 1711,NodeMinus26.w46,CompactMinus1696.checked1710,CompactMinus1696.small1710,CompactMinus1696.nodes1710,NodeMinus26.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1696.p1711,GridMinus.atNode 1711,GridMinus.atNode 1712,NodeMinus26.w47,CompactMinus1696.checked1711,CompactMinus1696.small1711,CompactMinus1696.nodes1711,NodeMinus26.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1712.p1712,GridMinus.atNode 1712,GridMinus.atNode 1713,NodeMinus26.w48,CompactMinus1712.checked1712,CompactMinus1712.small1712,CompactMinus1712.nodes1712,NodeMinus26.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1712.p1713,GridMinus.atNode 1713,GridMinus.atNode 1714,NodeMinus26.w49,CompactMinus1712.checked1713,CompactMinus1712.small1713,CompactMinus1712.nodes1713,NodeMinus26.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1712.p1714,GridMinus.atNode 1714,GridMinus.atNode 1715,NodeMinus26.w50,CompactMinus1712.checked1714,CompactMinus1712.small1714,CompactMinus1712.nodes1714,NodeMinus26.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1712.p1715,GridMinus.atNode 1715,GridMinus.atNode 1716,NodeMinus26.w51,CompactMinus1712.checked1715,CompactMinus1712.small1715,CompactMinus1712.nodes1715,NodeMinus26.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1712.p1716,GridMinus.atNode 1716,GridMinus.atNode 1717,NodeMinus26.w52,CompactMinus1712.checked1716,CompactMinus1712.small1716,CompactMinus1712.nodes1716,NodeMinus26.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1712.p1717,GridMinus.atNode 1717,GridMinus.atNode 1718,NodeMinus26.w53,CompactMinus1712.checked1717,CompactMinus1712.small1717,CompactMinus1712.nodes1717,NodeMinus26.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1712.p1718,GridMinus.atNode 1718,GridMinus.atNode 1719,NodeMinus26.w54,CompactMinus1712.checked1718,CompactMinus1712.small1718,CompactMinus1712.nodes1718,NodeMinus26.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1712.p1719,GridMinus.atNode 1719,GridMinus.atNode 1720,NodeMinus26.w55,CompactMinus1712.checked1719,CompactMinus1712.small1719,CompactMinus1712.nodes1719,NodeMinus26.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1712.p1720,GridMinus.atNode 1720,GridMinus.atNode 1721,NodeMinus26.w56,CompactMinus1712.checked1720,CompactMinus1712.small1720,CompactMinus1712.nodes1720,NodeMinus26.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1712.p1721,GridMinus.atNode 1721,GridMinus.atNode 1722,NodeMinus26.w57,CompactMinus1712.checked1721,CompactMinus1712.small1721,CompactMinus1712.nodes1721,NodeMinus26.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1712.p1722,GridMinus.atNode 1722,GridMinus.atNode 1723,NodeMinus26.w58,CompactMinus1712.checked1722,CompactMinus1712.small1722,CompactMinus1712.nodes1722,NodeMinus26.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1712.p1723,GridMinus.atNode 1723,GridMinus.atNode 1724,NodeMinus26.w59,CompactMinus1712.checked1723,CompactMinus1712.small1723,CompactMinus1712.nodes1723,NodeMinus26.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1712.p1724,GridMinus.atNode 1724,GridMinus.atNode 1725,NodeMinus26.w60,CompactMinus1712.checked1724,CompactMinus1712.small1724,CompactMinus1712.nodes1724,NodeMinus26.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1712.p1725,GridMinus.atNode 1725,GridMinus.atNode 1726,NodeMinus26.w61,CompactMinus1712.checked1725,CompactMinus1712.small1725,CompactMinus1712.nodes1725,NodeMinus26.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1712.p1726,GridMinus.atNode 1726,GridMinus.atNode 1727,NodeMinus26.w62,CompactMinus1712.checked1726,CompactMinus1712.small1726,CompactMinus1712.nodes1726,NodeMinus26.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1712.p1727,GridMinus.atNode 1727,GridMinus.atNode 1728,NodeMinus26.w63,CompactMinus1712.checked1727,CompactMinus1712.small1727,CompactMinus1712.nodes1727,NodeMinus26.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (1664+j) ∧
    (atRow j).right=GridMinus.atNode (1664+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus26
