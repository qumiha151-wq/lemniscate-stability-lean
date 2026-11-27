import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus1728
import SolitonClassification.Rotating.ResetPackedMinus1744
import SolitonClassification.Rotating.ResetPackedMinus1760
import SolitonClassification.Rotating.ResetPackedMinus1776
namespace SolitonClassification.Rotating.DyadicReset.TileMinus27
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1728.p1728,GridMinus.atNode 1728,GridMinus.atNode 1729,NodeMinus27.w0,CompactMinus1728.checked1728,CompactMinus1728.small1728,CompactMinus1728.nodes1728,NodeMinus27.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1728.p1729,GridMinus.atNode 1729,GridMinus.atNode 1730,NodeMinus27.w1,CompactMinus1728.checked1729,CompactMinus1728.small1729,CompactMinus1728.nodes1729,NodeMinus27.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1728.p1730,GridMinus.atNode 1730,GridMinus.atNode 1731,NodeMinus27.w2,CompactMinus1728.checked1730,CompactMinus1728.small1730,CompactMinus1728.nodes1730,NodeMinus27.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1728.p1731,GridMinus.atNode 1731,GridMinus.atNode 1732,NodeMinus27.w3,CompactMinus1728.checked1731,CompactMinus1728.small1731,CompactMinus1728.nodes1731,NodeMinus27.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1728.p1732,GridMinus.atNode 1732,GridMinus.atNode 1733,NodeMinus27.w4,CompactMinus1728.checked1732,CompactMinus1728.small1732,CompactMinus1728.nodes1732,NodeMinus27.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1728.p1733,GridMinus.atNode 1733,GridMinus.atNode 1734,NodeMinus27.w5,CompactMinus1728.checked1733,CompactMinus1728.small1733,CompactMinus1728.nodes1733,NodeMinus27.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1728.p1734,GridMinus.atNode 1734,GridMinus.atNode 1735,NodeMinus27.w6,CompactMinus1728.checked1734,CompactMinus1728.small1734,CompactMinus1728.nodes1734,NodeMinus27.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1728.p1735,GridMinus.atNode 1735,GridMinus.atNode 1736,NodeMinus27.w7,CompactMinus1728.checked1735,CompactMinus1728.small1735,CompactMinus1728.nodes1735,NodeMinus27.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1728.p1736,GridMinus.atNode 1736,GridMinus.atNode 1737,NodeMinus27.w8,CompactMinus1728.checked1736,CompactMinus1728.small1736,CompactMinus1728.nodes1736,NodeMinus27.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1728.p1737,GridMinus.atNode 1737,GridMinus.atNode 1738,NodeMinus27.w9,CompactMinus1728.checked1737,CompactMinus1728.small1737,CompactMinus1728.nodes1737,NodeMinus27.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1728.p1738,GridMinus.atNode 1738,GridMinus.atNode 1739,NodeMinus27.w10,CompactMinus1728.checked1738,CompactMinus1728.small1738,CompactMinus1728.nodes1738,NodeMinus27.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1728.p1739,GridMinus.atNode 1739,GridMinus.atNode 1740,NodeMinus27.w11,CompactMinus1728.checked1739,CompactMinus1728.small1739,CompactMinus1728.nodes1739,NodeMinus27.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1728.p1740,GridMinus.atNode 1740,GridMinus.atNode 1741,NodeMinus27.w12,CompactMinus1728.checked1740,CompactMinus1728.small1740,CompactMinus1728.nodes1740,NodeMinus27.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1728.p1741,GridMinus.atNode 1741,GridMinus.atNode 1742,NodeMinus27.w13,CompactMinus1728.checked1741,CompactMinus1728.small1741,CompactMinus1728.nodes1741,NodeMinus27.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1728.p1742,GridMinus.atNode 1742,GridMinus.atNode 1743,NodeMinus27.w14,CompactMinus1728.checked1742,CompactMinus1728.small1742,CompactMinus1728.nodes1742,NodeMinus27.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1728.p1743,GridMinus.atNode 1743,GridMinus.atNode 1744,NodeMinus27.w15,CompactMinus1728.checked1743,CompactMinus1728.small1743,CompactMinus1728.nodes1743,NodeMinus27.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1744.p1744,GridMinus.atNode 1744,GridMinus.atNode 1745,NodeMinus27.w16,CompactMinus1744.checked1744,CompactMinus1744.small1744,CompactMinus1744.nodes1744,NodeMinus27.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1744.p1745,GridMinus.atNode 1745,GridMinus.atNode 1746,NodeMinus27.w17,CompactMinus1744.checked1745,CompactMinus1744.small1745,CompactMinus1744.nodes1745,NodeMinus27.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1744.p1746,GridMinus.atNode 1746,GridMinus.atNode 1747,NodeMinus27.w18,CompactMinus1744.checked1746,CompactMinus1744.small1746,CompactMinus1744.nodes1746,NodeMinus27.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1744.p1747,GridMinus.atNode 1747,GridMinus.atNode 1748,NodeMinus27.w19,CompactMinus1744.checked1747,CompactMinus1744.small1747,CompactMinus1744.nodes1747,NodeMinus27.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1744.p1748,GridMinus.atNode 1748,GridMinus.atNode 1749,NodeMinus27.w20,CompactMinus1744.checked1748,CompactMinus1744.small1748,CompactMinus1744.nodes1748,NodeMinus27.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1744.p1749,GridMinus.atNode 1749,GridMinus.atNode 1750,NodeMinus27.w21,CompactMinus1744.checked1749,CompactMinus1744.small1749,CompactMinus1744.nodes1749,NodeMinus27.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1744.p1750,GridMinus.atNode 1750,GridMinus.atNode 1751,NodeMinus27.w22,CompactMinus1744.checked1750,CompactMinus1744.small1750,CompactMinus1744.nodes1750,NodeMinus27.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1744.p1751,GridMinus.atNode 1751,GridMinus.atNode 1752,NodeMinus27.w23,CompactMinus1744.checked1751,CompactMinus1744.small1751,CompactMinus1744.nodes1751,NodeMinus27.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1744.p1752,GridMinus.atNode 1752,GridMinus.atNode 1753,NodeMinus27.w24,CompactMinus1744.checked1752,CompactMinus1744.small1752,CompactMinus1744.nodes1752,NodeMinus27.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1744.p1753,GridMinus.atNode 1753,GridMinus.atNode 1754,NodeMinus27.w25,CompactMinus1744.checked1753,CompactMinus1744.small1753,CompactMinus1744.nodes1753,NodeMinus27.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1744.p1754,GridMinus.atNode 1754,GridMinus.atNode 1755,NodeMinus27.w26,CompactMinus1744.checked1754,CompactMinus1744.small1754,CompactMinus1744.nodes1754,NodeMinus27.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1744.p1755,GridMinus.atNode 1755,GridMinus.atNode 1756,NodeMinus27.w27,CompactMinus1744.checked1755,CompactMinus1744.small1755,CompactMinus1744.nodes1755,NodeMinus27.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1744.p1756,GridMinus.atNode 1756,GridMinus.atNode 1757,NodeMinus27.w28,CompactMinus1744.checked1756,CompactMinus1744.small1756,CompactMinus1744.nodes1756,NodeMinus27.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1744.p1757,GridMinus.atNode 1757,GridMinus.atNode 1758,NodeMinus27.w29,CompactMinus1744.checked1757,CompactMinus1744.small1757,CompactMinus1744.nodes1757,NodeMinus27.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1744.p1758,GridMinus.atNode 1758,GridMinus.atNode 1759,NodeMinus27.w30,CompactMinus1744.checked1758,CompactMinus1744.small1758,CompactMinus1744.nodes1758,NodeMinus27.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1744.p1759,GridMinus.atNode 1759,GridMinus.atNode 1760,NodeMinus27.w31,CompactMinus1744.checked1759,CompactMinus1744.small1759,CompactMinus1744.nodes1759,NodeMinus27.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1760.p1760,GridMinus.atNode 1760,GridMinus.atNode 1761,NodeMinus27.w32,CompactMinus1760.checked1760,CompactMinus1760.small1760,CompactMinus1760.nodes1760,NodeMinus27.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1760.p1761,GridMinus.atNode 1761,GridMinus.atNode 1762,NodeMinus27.w33,CompactMinus1760.checked1761,CompactMinus1760.small1761,CompactMinus1760.nodes1761,NodeMinus27.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1760.p1762,GridMinus.atNode 1762,GridMinus.atNode 1763,NodeMinus27.w34,CompactMinus1760.checked1762,CompactMinus1760.small1762,CompactMinus1760.nodes1762,NodeMinus27.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1760.p1763,GridMinus.atNode 1763,GridMinus.atNode 1764,NodeMinus27.w35,CompactMinus1760.checked1763,CompactMinus1760.small1763,CompactMinus1760.nodes1763,NodeMinus27.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1760.p1764,GridMinus.atNode 1764,GridMinus.atNode 1765,NodeMinus27.w36,CompactMinus1760.checked1764,CompactMinus1760.small1764,CompactMinus1760.nodes1764,NodeMinus27.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1760.p1765,GridMinus.atNode 1765,GridMinus.atNode 1766,NodeMinus27.w37,CompactMinus1760.checked1765,CompactMinus1760.small1765,CompactMinus1760.nodes1765,NodeMinus27.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1760.p1766,GridMinus.atNode 1766,GridMinus.atNode 1767,NodeMinus27.w38,CompactMinus1760.checked1766,CompactMinus1760.small1766,CompactMinus1760.nodes1766,NodeMinus27.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1760.p1767,GridMinus.atNode 1767,GridMinus.atNode 1768,NodeMinus27.w39,CompactMinus1760.checked1767,CompactMinus1760.small1767,CompactMinus1760.nodes1767,NodeMinus27.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1760.p1768,GridMinus.atNode 1768,GridMinus.atNode 1769,NodeMinus27.w40,CompactMinus1760.checked1768,CompactMinus1760.small1768,CompactMinus1760.nodes1768,NodeMinus27.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1760.p1769,GridMinus.atNode 1769,GridMinus.atNode 1770,NodeMinus27.w41,CompactMinus1760.checked1769,CompactMinus1760.small1769,CompactMinus1760.nodes1769,NodeMinus27.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1760.p1770,GridMinus.atNode 1770,GridMinus.atNode 1771,NodeMinus27.w42,CompactMinus1760.checked1770,CompactMinus1760.small1770,CompactMinus1760.nodes1770,NodeMinus27.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1760.p1771,GridMinus.atNode 1771,GridMinus.atNode 1772,NodeMinus27.w43,CompactMinus1760.checked1771,CompactMinus1760.small1771,CompactMinus1760.nodes1771,NodeMinus27.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1760.p1772,GridMinus.atNode 1772,GridMinus.atNode 1773,NodeMinus27.w44,CompactMinus1760.checked1772,CompactMinus1760.small1772,CompactMinus1760.nodes1772,NodeMinus27.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1760.p1773,GridMinus.atNode 1773,GridMinus.atNode 1774,NodeMinus27.w45,CompactMinus1760.checked1773,CompactMinus1760.small1773,CompactMinus1760.nodes1773,NodeMinus27.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1760.p1774,GridMinus.atNode 1774,GridMinus.atNode 1775,NodeMinus27.w46,CompactMinus1760.checked1774,CompactMinus1760.small1774,CompactMinus1760.nodes1774,NodeMinus27.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1760.p1775,GridMinus.atNode 1775,GridMinus.atNode 1776,NodeMinus27.w47,CompactMinus1760.checked1775,CompactMinus1760.small1775,CompactMinus1760.nodes1775,NodeMinus27.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1776.p1776,GridMinus.atNode 1776,GridMinus.atNode 1777,NodeMinus27.w48,CompactMinus1776.checked1776,CompactMinus1776.small1776,CompactMinus1776.nodes1776,NodeMinus27.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1776.p1777,GridMinus.atNode 1777,GridMinus.atNode 1778,NodeMinus27.w49,CompactMinus1776.checked1777,CompactMinus1776.small1777,CompactMinus1776.nodes1777,NodeMinus27.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1776.p1778,GridMinus.atNode 1778,GridMinus.atNode 1779,NodeMinus27.w50,CompactMinus1776.checked1778,CompactMinus1776.small1778,CompactMinus1776.nodes1778,NodeMinus27.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1776.p1779,GridMinus.atNode 1779,GridMinus.atNode 1780,NodeMinus27.w51,CompactMinus1776.checked1779,CompactMinus1776.small1779,CompactMinus1776.nodes1779,NodeMinus27.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1776.p1780,GridMinus.atNode 1780,GridMinus.atNode 1781,NodeMinus27.w52,CompactMinus1776.checked1780,CompactMinus1776.small1780,CompactMinus1776.nodes1780,NodeMinus27.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1776.p1781,GridMinus.atNode 1781,GridMinus.atNode 1782,NodeMinus27.w53,CompactMinus1776.checked1781,CompactMinus1776.small1781,CompactMinus1776.nodes1781,NodeMinus27.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1776.p1782,GridMinus.atNode 1782,GridMinus.atNode 1783,NodeMinus27.w54,CompactMinus1776.checked1782,CompactMinus1776.small1782,CompactMinus1776.nodes1782,NodeMinus27.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1776.p1783,GridMinus.atNode 1783,GridMinus.atNode 1784,NodeMinus27.w55,CompactMinus1776.checked1783,CompactMinus1776.small1783,CompactMinus1776.nodes1783,NodeMinus27.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1776.p1784,GridMinus.atNode 1784,GridMinus.atNode 1785,NodeMinus27.w56,CompactMinus1776.checked1784,CompactMinus1776.small1784,CompactMinus1776.nodes1784,NodeMinus27.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1776.p1785,GridMinus.atNode 1785,GridMinus.atNode 1786,NodeMinus27.w57,CompactMinus1776.checked1785,CompactMinus1776.small1785,CompactMinus1776.nodes1785,NodeMinus27.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1776.p1786,GridMinus.atNode 1786,GridMinus.atNode 1787,NodeMinus27.w58,CompactMinus1776.checked1786,CompactMinus1776.small1786,CompactMinus1776.nodes1786,NodeMinus27.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1776.p1787,GridMinus.atNode 1787,GridMinus.atNode 1788,NodeMinus27.w59,CompactMinus1776.checked1787,CompactMinus1776.small1787,CompactMinus1776.nodes1787,NodeMinus27.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1776.p1788,GridMinus.atNode 1788,GridMinus.atNode 1789,NodeMinus27.w60,CompactMinus1776.checked1788,CompactMinus1776.small1788,CompactMinus1776.nodes1788,NodeMinus27.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1776.p1789,GridMinus.atNode 1789,GridMinus.atNode 1790,NodeMinus27.w61,CompactMinus1776.checked1789,CompactMinus1776.small1789,CompactMinus1776.nodes1789,NodeMinus27.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1776.p1790,GridMinus.atNode 1790,GridMinus.atNode 1791,NodeMinus27.w62,CompactMinus1776.checked1790,CompactMinus1776.small1790,CompactMinus1776.nodes1790,NodeMinus27.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1776.p1791,GridMinus.atNode 1791,GridMinus.atNode 1792,NodeMinus27.w63,CompactMinus1776.checked1791,CompactMinus1776.small1791,CompactMinus1776.nodes1791,NodeMinus27.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (1728+j) ∧
    (atRow j).right=GridMinus.atNode (1728+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus27
