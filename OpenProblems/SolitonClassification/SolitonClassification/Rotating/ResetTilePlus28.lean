import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus1792
import SolitonClassification.Rotating.ResetPackedPlus1808
import SolitonClassification.Rotating.ResetPackedPlus1824
import SolitonClassification.Rotating.ResetPackedPlus1840
namespace SolitonClassification.Rotating.DyadicReset.TilePlus28
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus1792.p1792,GridPlus.atNode 1792,GridPlus.atNode 1793,NodePlus28.w0,CompactPlus1792.checked1792,CompactPlus1792.small1792,CompactPlus1792.nodes1792,NodePlus28.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus1792.p1793,GridPlus.atNode 1793,GridPlus.atNode 1794,NodePlus28.w1,CompactPlus1792.checked1793,CompactPlus1792.small1793,CompactPlus1792.nodes1793,NodePlus28.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus1792.p1794,GridPlus.atNode 1794,GridPlus.atNode 1795,NodePlus28.w2,CompactPlus1792.checked1794,CompactPlus1792.small1794,CompactPlus1792.nodes1794,NodePlus28.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus1792.p1795,GridPlus.atNode 1795,GridPlus.atNode 1796,NodePlus28.w3,CompactPlus1792.checked1795,CompactPlus1792.small1795,CompactPlus1792.nodes1795,NodePlus28.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus1792.p1796,GridPlus.atNode 1796,GridPlus.atNode 1797,NodePlus28.w4,CompactPlus1792.checked1796,CompactPlus1792.small1796,CompactPlus1792.nodes1796,NodePlus28.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus1792.p1797,GridPlus.atNode 1797,GridPlus.atNode 1798,NodePlus28.w5,CompactPlus1792.checked1797,CompactPlus1792.small1797,CompactPlus1792.nodes1797,NodePlus28.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus1792.p1798,GridPlus.atNode 1798,GridPlus.atNode 1799,NodePlus28.w6,CompactPlus1792.checked1798,CompactPlus1792.small1798,CompactPlus1792.nodes1798,NodePlus28.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus1792.p1799,GridPlus.atNode 1799,GridPlus.atNode 1800,NodePlus28.w7,CompactPlus1792.checked1799,CompactPlus1792.small1799,CompactPlus1792.nodes1799,NodePlus28.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus1792.p1800,GridPlus.atNode 1800,GridPlus.atNode 1801,NodePlus28.w8,CompactPlus1792.checked1800,CompactPlus1792.small1800,CompactPlus1792.nodes1800,NodePlus28.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus1792.p1801,GridPlus.atNode 1801,GridPlus.atNode 1802,NodePlus28.w9,CompactPlus1792.checked1801,CompactPlus1792.small1801,CompactPlus1792.nodes1801,NodePlus28.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus1792.p1802,GridPlus.atNode 1802,GridPlus.atNode 1803,NodePlus28.w10,CompactPlus1792.checked1802,CompactPlus1792.small1802,CompactPlus1792.nodes1802,NodePlus28.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus1792.p1803,GridPlus.atNode 1803,GridPlus.atNode 1804,NodePlus28.w11,CompactPlus1792.checked1803,CompactPlus1792.small1803,CompactPlus1792.nodes1803,NodePlus28.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus1792.p1804,GridPlus.atNode 1804,GridPlus.atNode 1805,NodePlus28.w12,CompactPlus1792.checked1804,CompactPlus1792.small1804,CompactPlus1792.nodes1804,NodePlus28.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus1792.p1805,GridPlus.atNode 1805,GridPlus.atNode 1806,NodePlus28.w13,CompactPlus1792.checked1805,CompactPlus1792.small1805,CompactPlus1792.nodes1805,NodePlus28.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus1792.p1806,GridPlus.atNode 1806,GridPlus.atNode 1807,NodePlus28.w14,CompactPlus1792.checked1806,CompactPlus1792.small1806,CompactPlus1792.nodes1806,NodePlus28.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus1792.p1807,GridPlus.atNode 1807,GridPlus.atNode 1808,NodePlus28.w15,CompactPlus1792.checked1807,CompactPlus1792.small1807,CompactPlus1792.nodes1807,NodePlus28.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus1808.p1808,GridPlus.atNode 1808,GridPlus.atNode 1809,NodePlus28.w16,CompactPlus1808.checked1808,CompactPlus1808.small1808,CompactPlus1808.nodes1808,NodePlus28.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus1808.p1809,GridPlus.atNode 1809,GridPlus.atNode 1810,NodePlus28.w17,CompactPlus1808.checked1809,CompactPlus1808.small1809,CompactPlus1808.nodes1809,NodePlus28.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus1808.p1810,GridPlus.atNode 1810,GridPlus.atNode 1811,NodePlus28.w18,CompactPlus1808.checked1810,CompactPlus1808.small1810,CompactPlus1808.nodes1810,NodePlus28.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus1808.p1811,GridPlus.atNode 1811,GridPlus.atNode 1812,NodePlus28.w19,CompactPlus1808.checked1811,CompactPlus1808.small1811,CompactPlus1808.nodes1811,NodePlus28.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus1808.p1812,GridPlus.atNode 1812,GridPlus.atNode 1813,NodePlus28.w20,CompactPlus1808.checked1812,CompactPlus1808.small1812,CompactPlus1808.nodes1812,NodePlus28.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus1808.p1813,GridPlus.atNode 1813,GridPlus.atNode 1814,NodePlus28.w21,CompactPlus1808.checked1813,CompactPlus1808.small1813,CompactPlus1808.nodes1813,NodePlus28.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus1808.p1814,GridPlus.atNode 1814,GridPlus.atNode 1815,NodePlus28.w22,CompactPlus1808.checked1814,CompactPlus1808.small1814,CompactPlus1808.nodes1814,NodePlus28.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus1808.p1815,GridPlus.atNode 1815,GridPlus.atNode 1816,NodePlus28.w23,CompactPlus1808.checked1815,CompactPlus1808.small1815,CompactPlus1808.nodes1815,NodePlus28.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus1808.p1816,GridPlus.atNode 1816,GridPlus.atNode 1817,NodePlus28.w24,CompactPlus1808.checked1816,CompactPlus1808.small1816,CompactPlus1808.nodes1816,NodePlus28.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus1808.p1817,GridPlus.atNode 1817,GridPlus.atNode 1818,NodePlus28.w25,CompactPlus1808.checked1817,CompactPlus1808.small1817,CompactPlus1808.nodes1817,NodePlus28.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus1808.p1818,GridPlus.atNode 1818,GridPlus.atNode 1819,NodePlus28.w26,CompactPlus1808.checked1818,CompactPlus1808.small1818,CompactPlus1808.nodes1818,NodePlus28.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus1808.p1819,GridPlus.atNode 1819,GridPlus.atNode 1820,NodePlus28.w27,CompactPlus1808.checked1819,CompactPlus1808.small1819,CompactPlus1808.nodes1819,NodePlus28.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus1808.p1820,GridPlus.atNode 1820,GridPlus.atNode 1821,NodePlus28.w28,CompactPlus1808.checked1820,CompactPlus1808.small1820,CompactPlus1808.nodes1820,NodePlus28.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus1808.p1821,GridPlus.atNode 1821,GridPlus.atNode 1822,NodePlus28.w29,CompactPlus1808.checked1821,CompactPlus1808.small1821,CompactPlus1808.nodes1821,NodePlus28.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus1808.p1822,GridPlus.atNode 1822,GridPlus.atNode 1823,NodePlus28.w30,CompactPlus1808.checked1822,CompactPlus1808.small1822,CompactPlus1808.nodes1822,NodePlus28.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus1808.p1823,GridPlus.atNode 1823,GridPlus.atNode 1824,NodePlus28.w31,CompactPlus1808.checked1823,CompactPlus1808.small1823,CompactPlus1808.nodes1823,NodePlus28.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus1824.p1824,GridPlus.atNode 1824,GridPlus.atNode 1825,NodePlus28.w32,CompactPlus1824.checked1824,CompactPlus1824.small1824,CompactPlus1824.nodes1824,NodePlus28.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus1824.p1825,GridPlus.atNode 1825,GridPlus.atNode 1826,NodePlus28.w33,CompactPlus1824.checked1825,CompactPlus1824.small1825,CompactPlus1824.nodes1825,NodePlus28.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus1824.p1826,GridPlus.atNode 1826,GridPlus.atNode 1827,NodePlus28.w34,CompactPlus1824.checked1826,CompactPlus1824.small1826,CompactPlus1824.nodes1826,NodePlus28.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus1824.p1827,GridPlus.atNode 1827,GridPlus.atNode 1828,NodePlus28.w35,CompactPlus1824.checked1827,CompactPlus1824.small1827,CompactPlus1824.nodes1827,NodePlus28.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus1824.p1828,GridPlus.atNode 1828,GridPlus.atNode 1829,NodePlus28.w36,CompactPlus1824.checked1828,CompactPlus1824.small1828,CompactPlus1824.nodes1828,NodePlus28.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus1824.p1829,GridPlus.atNode 1829,GridPlus.atNode 1830,NodePlus28.w37,CompactPlus1824.checked1829,CompactPlus1824.small1829,CompactPlus1824.nodes1829,NodePlus28.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus1824.p1830,GridPlus.atNode 1830,GridPlus.atNode 1831,NodePlus28.w38,CompactPlus1824.checked1830,CompactPlus1824.small1830,CompactPlus1824.nodes1830,NodePlus28.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus1824.p1831,GridPlus.atNode 1831,GridPlus.atNode 1832,NodePlus28.w39,CompactPlus1824.checked1831,CompactPlus1824.small1831,CompactPlus1824.nodes1831,NodePlus28.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus1824.p1832,GridPlus.atNode 1832,GridPlus.atNode 1833,NodePlus28.w40,CompactPlus1824.checked1832,CompactPlus1824.small1832,CompactPlus1824.nodes1832,NodePlus28.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus1824.p1833,GridPlus.atNode 1833,GridPlus.atNode 1834,NodePlus28.w41,CompactPlus1824.checked1833,CompactPlus1824.small1833,CompactPlus1824.nodes1833,NodePlus28.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus1824.p1834,GridPlus.atNode 1834,GridPlus.atNode 1835,NodePlus28.w42,CompactPlus1824.checked1834,CompactPlus1824.small1834,CompactPlus1824.nodes1834,NodePlus28.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus1824.p1835,GridPlus.atNode 1835,GridPlus.atNode 1836,NodePlus28.w43,CompactPlus1824.checked1835,CompactPlus1824.small1835,CompactPlus1824.nodes1835,NodePlus28.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus1824.p1836,GridPlus.atNode 1836,GridPlus.atNode 1837,NodePlus28.w44,CompactPlus1824.checked1836,CompactPlus1824.small1836,CompactPlus1824.nodes1836,NodePlus28.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus1824.p1837,GridPlus.atNode 1837,GridPlus.atNode 1838,NodePlus28.w45,CompactPlus1824.checked1837,CompactPlus1824.small1837,CompactPlus1824.nodes1837,NodePlus28.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus1824.p1838,GridPlus.atNode 1838,GridPlus.atNode 1839,NodePlus28.w46,CompactPlus1824.checked1838,CompactPlus1824.small1838,CompactPlus1824.nodes1838,NodePlus28.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus1824.p1839,GridPlus.atNode 1839,GridPlus.atNode 1840,NodePlus28.w47,CompactPlus1824.checked1839,CompactPlus1824.small1839,CompactPlus1824.nodes1839,NodePlus28.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus1840.p1840,GridPlus.atNode 1840,GridPlus.atNode 1841,NodePlus28.w48,CompactPlus1840.checked1840,CompactPlus1840.small1840,CompactPlus1840.nodes1840,NodePlus28.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus1840.p1841,GridPlus.atNode 1841,GridPlus.atNode 1842,NodePlus28.w49,CompactPlus1840.checked1841,CompactPlus1840.small1841,CompactPlus1840.nodes1841,NodePlus28.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus1840.p1842,GridPlus.atNode 1842,GridPlus.atNode 1843,NodePlus28.w50,CompactPlus1840.checked1842,CompactPlus1840.small1842,CompactPlus1840.nodes1842,NodePlus28.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus1840.p1843,GridPlus.atNode 1843,GridPlus.atNode 1844,NodePlus28.w51,CompactPlus1840.checked1843,CompactPlus1840.small1843,CompactPlus1840.nodes1843,NodePlus28.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus1840.p1844,GridPlus.atNode 1844,GridPlus.atNode 1845,NodePlus28.w52,CompactPlus1840.checked1844,CompactPlus1840.small1844,CompactPlus1840.nodes1844,NodePlus28.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus1840.p1845,GridPlus.atNode 1845,GridPlus.atNode 1846,NodePlus28.w53,CompactPlus1840.checked1845,CompactPlus1840.small1845,CompactPlus1840.nodes1845,NodePlus28.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus1840.p1846,GridPlus.atNode 1846,GridPlus.atNode 1847,NodePlus28.w54,CompactPlus1840.checked1846,CompactPlus1840.small1846,CompactPlus1840.nodes1846,NodePlus28.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus1840.p1847,GridPlus.atNode 1847,GridPlus.atNode 1848,NodePlus28.w55,CompactPlus1840.checked1847,CompactPlus1840.small1847,CompactPlus1840.nodes1847,NodePlus28.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus1840.p1848,GridPlus.atNode 1848,GridPlus.atNode 1849,NodePlus28.w56,CompactPlus1840.checked1848,CompactPlus1840.small1848,CompactPlus1840.nodes1848,NodePlus28.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus1840.p1849,GridPlus.atNode 1849,GridPlus.atNode 1850,NodePlus28.w57,CompactPlus1840.checked1849,CompactPlus1840.small1849,CompactPlus1840.nodes1849,NodePlus28.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus1840.p1850,GridPlus.atNode 1850,GridPlus.atNode 1851,NodePlus28.w58,CompactPlus1840.checked1850,CompactPlus1840.small1850,CompactPlus1840.nodes1850,NodePlus28.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus1840.p1851,GridPlus.atNode 1851,GridPlus.atNode 1852,NodePlus28.w59,CompactPlus1840.checked1851,CompactPlus1840.small1851,CompactPlus1840.nodes1851,NodePlus28.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus1840.p1852,GridPlus.atNode 1852,GridPlus.atNode 1853,NodePlus28.w60,CompactPlus1840.checked1852,CompactPlus1840.small1852,CompactPlus1840.nodes1852,NodePlus28.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus1840.p1853,GridPlus.atNode 1853,GridPlus.atNode 1854,NodePlus28.w61,CompactPlus1840.checked1853,CompactPlus1840.small1853,CompactPlus1840.nodes1853,NodePlus28.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus1840.p1854,GridPlus.atNode 1854,GridPlus.atNode 1855,NodePlus28.w62,CompactPlus1840.checked1854,CompactPlus1840.small1854,CompactPlus1840.nodes1854,NodePlus28.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus1840.p1855,GridPlus.atNode 1855,GridPlus.atNode 1856,NodePlus28.w63,CompactPlus1840.checked1855,CompactPlus1840.small1855,CompactPlus1840.nodes1855,NodePlus28.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (1792+j) ∧
    (atRow j).right=GridPlus.atNode (1792+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus28
