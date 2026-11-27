import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus1728
import SolitonClassification.Rotating.ResetPackedPlus1744
import SolitonClassification.Rotating.ResetPackedPlus1760
import SolitonClassification.Rotating.ResetPackedPlus1776
namespace SolitonClassification.Rotating.DyadicReset.TilePlus27
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus1728.p1728,GridPlus.atNode 1728,GridPlus.atNode 1729,NodePlus27.w0,CompactPlus1728.checked1728,CompactPlus1728.small1728,CompactPlus1728.nodes1728,NodePlus27.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus1728.p1729,GridPlus.atNode 1729,GridPlus.atNode 1730,NodePlus27.w1,CompactPlus1728.checked1729,CompactPlus1728.small1729,CompactPlus1728.nodes1729,NodePlus27.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus1728.p1730,GridPlus.atNode 1730,GridPlus.atNode 1731,NodePlus27.w2,CompactPlus1728.checked1730,CompactPlus1728.small1730,CompactPlus1728.nodes1730,NodePlus27.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus1728.p1731,GridPlus.atNode 1731,GridPlus.atNode 1732,NodePlus27.w3,CompactPlus1728.checked1731,CompactPlus1728.small1731,CompactPlus1728.nodes1731,NodePlus27.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus1728.p1732,GridPlus.atNode 1732,GridPlus.atNode 1733,NodePlus27.w4,CompactPlus1728.checked1732,CompactPlus1728.small1732,CompactPlus1728.nodes1732,NodePlus27.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus1728.p1733,GridPlus.atNode 1733,GridPlus.atNode 1734,NodePlus27.w5,CompactPlus1728.checked1733,CompactPlus1728.small1733,CompactPlus1728.nodes1733,NodePlus27.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus1728.p1734,GridPlus.atNode 1734,GridPlus.atNode 1735,NodePlus27.w6,CompactPlus1728.checked1734,CompactPlus1728.small1734,CompactPlus1728.nodes1734,NodePlus27.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus1728.p1735,GridPlus.atNode 1735,GridPlus.atNode 1736,NodePlus27.w7,CompactPlus1728.checked1735,CompactPlus1728.small1735,CompactPlus1728.nodes1735,NodePlus27.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus1728.p1736,GridPlus.atNode 1736,GridPlus.atNode 1737,NodePlus27.w8,CompactPlus1728.checked1736,CompactPlus1728.small1736,CompactPlus1728.nodes1736,NodePlus27.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus1728.p1737,GridPlus.atNode 1737,GridPlus.atNode 1738,NodePlus27.w9,CompactPlus1728.checked1737,CompactPlus1728.small1737,CompactPlus1728.nodes1737,NodePlus27.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus1728.p1738,GridPlus.atNode 1738,GridPlus.atNode 1739,NodePlus27.w10,CompactPlus1728.checked1738,CompactPlus1728.small1738,CompactPlus1728.nodes1738,NodePlus27.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus1728.p1739,GridPlus.atNode 1739,GridPlus.atNode 1740,NodePlus27.w11,CompactPlus1728.checked1739,CompactPlus1728.small1739,CompactPlus1728.nodes1739,NodePlus27.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus1728.p1740,GridPlus.atNode 1740,GridPlus.atNode 1741,NodePlus27.w12,CompactPlus1728.checked1740,CompactPlus1728.small1740,CompactPlus1728.nodes1740,NodePlus27.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus1728.p1741,GridPlus.atNode 1741,GridPlus.atNode 1742,NodePlus27.w13,CompactPlus1728.checked1741,CompactPlus1728.small1741,CompactPlus1728.nodes1741,NodePlus27.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus1728.p1742,GridPlus.atNode 1742,GridPlus.atNode 1743,NodePlus27.w14,CompactPlus1728.checked1742,CompactPlus1728.small1742,CompactPlus1728.nodes1742,NodePlus27.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus1728.p1743,GridPlus.atNode 1743,GridPlus.atNode 1744,NodePlus27.w15,CompactPlus1728.checked1743,CompactPlus1728.small1743,CompactPlus1728.nodes1743,NodePlus27.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus1744.p1744,GridPlus.atNode 1744,GridPlus.atNode 1745,NodePlus27.w16,CompactPlus1744.checked1744,CompactPlus1744.small1744,CompactPlus1744.nodes1744,NodePlus27.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus1744.p1745,GridPlus.atNode 1745,GridPlus.atNode 1746,NodePlus27.w17,CompactPlus1744.checked1745,CompactPlus1744.small1745,CompactPlus1744.nodes1745,NodePlus27.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus1744.p1746,GridPlus.atNode 1746,GridPlus.atNode 1747,NodePlus27.w18,CompactPlus1744.checked1746,CompactPlus1744.small1746,CompactPlus1744.nodes1746,NodePlus27.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus1744.p1747,GridPlus.atNode 1747,GridPlus.atNode 1748,NodePlus27.w19,CompactPlus1744.checked1747,CompactPlus1744.small1747,CompactPlus1744.nodes1747,NodePlus27.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus1744.p1748,GridPlus.atNode 1748,GridPlus.atNode 1749,NodePlus27.w20,CompactPlus1744.checked1748,CompactPlus1744.small1748,CompactPlus1744.nodes1748,NodePlus27.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus1744.p1749,GridPlus.atNode 1749,GridPlus.atNode 1750,NodePlus27.w21,CompactPlus1744.checked1749,CompactPlus1744.small1749,CompactPlus1744.nodes1749,NodePlus27.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus1744.p1750,GridPlus.atNode 1750,GridPlus.atNode 1751,NodePlus27.w22,CompactPlus1744.checked1750,CompactPlus1744.small1750,CompactPlus1744.nodes1750,NodePlus27.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus1744.p1751,GridPlus.atNode 1751,GridPlus.atNode 1752,NodePlus27.w23,CompactPlus1744.checked1751,CompactPlus1744.small1751,CompactPlus1744.nodes1751,NodePlus27.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus1744.p1752,GridPlus.atNode 1752,GridPlus.atNode 1753,NodePlus27.w24,CompactPlus1744.checked1752,CompactPlus1744.small1752,CompactPlus1744.nodes1752,NodePlus27.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus1744.p1753,GridPlus.atNode 1753,GridPlus.atNode 1754,NodePlus27.w25,CompactPlus1744.checked1753,CompactPlus1744.small1753,CompactPlus1744.nodes1753,NodePlus27.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus1744.p1754,GridPlus.atNode 1754,GridPlus.atNode 1755,NodePlus27.w26,CompactPlus1744.checked1754,CompactPlus1744.small1754,CompactPlus1744.nodes1754,NodePlus27.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus1744.p1755,GridPlus.atNode 1755,GridPlus.atNode 1756,NodePlus27.w27,CompactPlus1744.checked1755,CompactPlus1744.small1755,CompactPlus1744.nodes1755,NodePlus27.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus1744.p1756,GridPlus.atNode 1756,GridPlus.atNode 1757,NodePlus27.w28,CompactPlus1744.checked1756,CompactPlus1744.small1756,CompactPlus1744.nodes1756,NodePlus27.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus1744.p1757,GridPlus.atNode 1757,GridPlus.atNode 1758,NodePlus27.w29,CompactPlus1744.checked1757,CompactPlus1744.small1757,CompactPlus1744.nodes1757,NodePlus27.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus1744.p1758,GridPlus.atNode 1758,GridPlus.atNode 1759,NodePlus27.w30,CompactPlus1744.checked1758,CompactPlus1744.small1758,CompactPlus1744.nodes1758,NodePlus27.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus1744.p1759,GridPlus.atNode 1759,GridPlus.atNode 1760,NodePlus27.w31,CompactPlus1744.checked1759,CompactPlus1744.small1759,CompactPlus1744.nodes1759,NodePlus27.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus1760.p1760,GridPlus.atNode 1760,GridPlus.atNode 1761,NodePlus27.w32,CompactPlus1760.checked1760,CompactPlus1760.small1760,CompactPlus1760.nodes1760,NodePlus27.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus1760.p1761,GridPlus.atNode 1761,GridPlus.atNode 1762,NodePlus27.w33,CompactPlus1760.checked1761,CompactPlus1760.small1761,CompactPlus1760.nodes1761,NodePlus27.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus1760.p1762,GridPlus.atNode 1762,GridPlus.atNode 1763,NodePlus27.w34,CompactPlus1760.checked1762,CompactPlus1760.small1762,CompactPlus1760.nodes1762,NodePlus27.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus1760.p1763,GridPlus.atNode 1763,GridPlus.atNode 1764,NodePlus27.w35,CompactPlus1760.checked1763,CompactPlus1760.small1763,CompactPlus1760.nodes1763,NodePlus27.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus1760.p1764,GridPlus.atNode 1764,GridPlus.atNode 1765,NodePlus27.w36,CompactPlus1760.checked1764,CompactPlus1760.small1764,CompactPlus1760.nodes1764,NodePlus27.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus1760.p1765,GridPlus.atNode 1765,GridPlus.atNode 1766,NodePlus27.w37,CompactPlus1760.checked1765,CompactPlus1760.small1765,CompactPlus1760.nodes1765,NodePlus27.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus1760.p1766,GridPlus.atNode 1766,GridPlus.atNode 1767,NodePlus27.w38,CompactPlus1760.checked1766,CompactPlus1760.small1766,CompactPlus1760.nodes1766,NodePlus27.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus1760.p1767,GridPlus.atNode 1767,GridPlus.atNode 1768,NodePlus27.w39,CompactPlus1760.checked1767,CompactPlus1760.small1767,CompactPlus1760.nodes1767,NodePlus27.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus1760.p1768,GridPlus.atNode 1768,GridPlus.atNode 1769,NodePlus27.w40,CompactPlus1760.checked1768,CompactPlus1760.small1768,CompactPlus1760.nodes1768,NodePlus27.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus1760.p1769,GridPlus.atNode 1769,GridPlus.atNode 1770,NodePlus27.w41,CompactPlus1760.checked1769,CompactPlus1760.small1769,CompactPlus1760.nodes1769,NodePlus27.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus1760.p1770,GridPlus.atNode 1770,GridPlus.atNode 1771,NodePlus27.w42,CompactPlus1760.checked1770,CompactPlus1760.small1770,CompactPlus1760.nodes1770,NodePlus27.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus1760.p1771,GridPlus.atNode 1771,GridPlus.atNode 1772,NodePlus27.w43,CompactPlus1760.checked1771,CompactPlus1760.small1771,CompactPlus1760.nodes1771,NodePlus27.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus1760.p1772,GridPlus.atNode 1772,GridPlus.atNode 1773,NodePlus27.w44,CompactPlus1760.checked1772,CompactPlus1760.small1772,CompactPlus1760.nodes1772,NodePlus27.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus1760.p1773,GridPlus.atNode 1773,GridPlus.atNode 1774,NodePlus27.w45,CompactPlus1760.checked1773,CompactPlus1760.small1773,CompactPlus1760.nodes1773,NodePlus27.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus1760.p1774,GridPlus.atNode 1774,GridPlus.atNode 1775,NodePlus27.w46,CompactPlus1760.checked1774,CompactPlus1760.small1774,CompactPlus1760.nodes1774,NodePlus27.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus1760.p1775,GridPlus.atNode 1775,GridPlus.atNode 1776,NodePlus27.w47,CompactPlus1760.checked1775,CompactPlus1760.small1775,CompactPlus1760.nodes1775,NodePlus27.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus1776.p1776,GridPlus.atNode 1776,GridPlus.atNode 1777,NodePlus27.w48,CompactPlus1776.checked1776,CompactPlus1776.small1776,CompactPlus1776.nodes1776,NodePlus27.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus1776.p1777,GridPlus.atNode 1777,GridPlus.atNode 1778,NodePlus27.w49,CompactPlus1776.checked1777,CompactPlus1776.small1777,CompactPlus1776.nodes1777,NodePlus27.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus1776.p1778,GridPlus.atNode 1778,GridPlus.atNode 1779,NodePlus27.w50,CompactPlus1776.checked1778,CompactPlus1776.small1778,CompactPlus1776.nodes1778,NodePlus27.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus1776.p1779,GridPlus.atNode 1779,GridPlus.atNode 1780,NodePlus27.w51,CompactPlus1776.checked1779,CompactPlus1776.small1779,CompactPlus1776.nodes1779,NodePlus27.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus1776.p1780,GridPlus.atNode 1780,GridPlus.atNode 1781,NodePlus27.w52,CompactPlus1776.checked1780,CompactPlus1776.small1780,CompactPlus1776.nodes1780,NodePlus27.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus1776.p1781,GridPlus.atNode 1781,GridPlus.atNode 1782,NodePlus27.w53,CompactPlus1776.checked1781,CompactPlus1776.small1781,CompactPlus1776.nodes1781,NodePlus27.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus1776.p1782,GridPlus.atNode 1782,GridPlus.atNode 1783,NodePlus27.w54,CompactPlus1776.checked1782,CompactPlus1776.small1782,CompactPlus1776.nodes1782,NodePlus27.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus1776.p1783,GridPlus.atNode 1783,GridPlus.atNode 1784,NodePlus27.w55,CompactPlus1776.checked1783,CompactPlus1776.small1783,CompactPlus1776.nodes1783,NodePlus27.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus1776.p1784,GridPlus.atNode 1784,GridPlus.atNode 1785,NodePlus27.w56,CompactPlus1776.checked1784,CompactPlus1776.small1784,CompactPlus1776.nodes1784,NodePlus27.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus1776.p1785,GridPlus.atNode 1785,GridPlus.atNode 1786,NodePlus27.w57,CompactPlus1776.checked1785,CompactPlus1776.small1785,CompactPlus1776.nodes1785,NodePlus27.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus1776.p1786,GridPlus.atNode 1786,GridPlus.atNode 1787,NodePlus27.w58,CompactPlus1776.checked1786,CompactPlus1776.small1786,CompactPlus1776.nodes1786,NodePlus27.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus1776.p1787,GridPlus.atNode 1787,GridPlus.atNode 1788,NodePlus27.w59,CompactPlus1776.checked1787,CompactPlus1776.small1787,CompactPlus1776.nodes1787,NodePlus27.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus1776.p1788,GridPlus.atNode 1788,GridPlus.atNode 1789,NodePlus27.w60,CompactPlus1776.checked1788,CompactPlus1776.small1788,CompactPlus1776.nodes1788,NodePlus27.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus1776.p1789,GridPlus.atNode 1789,GridPlus.atNode 1790,NodePlus27.w61,CompactPlus1776.checked1789,CompactPlus1776.small1789,CompactPlus1776.nodes1789,NodePlus27.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus1776.p1790,GridPlus.atNode 1790,GridPlus.atNode 1791,NodePlus27.w62,CompactPlus1776.checked1790,CompactPlus1776.small1790,CompactPlus1776.nodes1790,NodePlus27.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus1776.p1791,GridPlus.atNode 1791,GridPlus.atNode 1792,NodePlus27.w63,CompactPlus1776.checked1791,CompactPlus1776.small1791,CompactPlus1776.nodes1791,NodePlus27.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (1728+j) ∧
    (atRow j).right=GridPlus.atNode (1728+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus27
