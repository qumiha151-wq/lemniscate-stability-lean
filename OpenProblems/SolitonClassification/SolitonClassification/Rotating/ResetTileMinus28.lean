import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus1792
import SolitonClassification.Rotating.ResetPackedMinus1808
import SolitonClassification.Rotating.ResetPackedMinus1824
import SolitonClassification.Rotating.ResetPackedMinus1840
namespace SolitonClassification.Rotating.DyadicReset.TileMinus28
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1792.p1792,GridMinus.atNode 1792,GridMinus.atNode 1793,NodeMinus28.w0,CompactMinus1792.checked1792,CompactMinus1792.small1792,CompactMinus1792.nodes1792,NodeMinus28.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1792.p1793,GridMinus.atNode 1793,GridMinus.atNode 1794,NodeMinus28.w1,CompactMinus1792.checked1793,CompactMinus1792.small1793,CompactMinus1792.nodes1793,NodeMinus28.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1792.p1794,GridMinus.atNode 1794,GridMinus.atNode 1795,NodeMinus28.w2,CompactMinus1792.checked1794,CompactMinus1792.small1794,CompactMinus1792.nodes1794,NodeMinus28.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1792.p1795,GridMinus.atNode 1795,GridMinus.atNode 1796,NodeMinus28.w3,CompactMinus1792.checked1795,CompactMinus1792.small1795,CompactMinus1792.nodes1795,NodeMinus28.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1792.p1796,GridMinus.atNode 1796,GridMinus.atNode 1797,NodeMinus28.w4,CompactMinus1792.checked1796,CompactMinus1792.small1796,CompactMinus1792.nodes1796,NodeMinus28.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1792.p1797,GridMinus.atNode 1797,GridMinus.atNode 1798,NodeMinus28.w5,CompactMinus1792.checked1797,CompactMinus1792.small1797,CompactMinus1792.nodes1797,NodeMinus28.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1792.p1798,GridMinus.atNode 1798,GridMinus.atNode 1799,NodeMinus28.w6,CompactMinus1792.checked1798,CompactMinus1792.small1798,CompactMinus1792.nodes1798,NodeMinus28.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1792.p1799,GridMinus.atNode 1799,GridMinus.atNode 1800,NodeMinus28.w7,CompactMinus1792.checked1799,CompactMinus1792.small1799,CompactMinus1792.nodes1799,NodeMinus28.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1792.p1800,GridMinus.atNode 1800,GridMinus.atNode 1801,NodeMinus28.w8,CompactMinus1792.checked1800,CompactMinus1792.small1800,CompactMinus1792.nodes1800,NodeMinus28.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1792.p1801,GridMinus.atNode 1801,GridMinus.atNode 1802,NodeMinus28.w9,CompactMinus1792.checked1801,CompactMinus1792.small1801,CompactMinus1792.nodes1801,NodeMinus28.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1792.p1802,GridMinus.atNode 1802,GridMinus.atNode 1803,NodeMinus28.w10,CompactMinus1792.checked1802,CompactMinus1792.small1802,CompactMinus1792.nodes1802,NodeMinus28.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1792.p1803,GridMinus.atNode 1803,GridMinus.atNode 1804,NodeMinus28.w11,CompactMinus1792.checked1803,CompactMinus1792.small1803,CompactMinus1792.nodes1803,NodeMinus28.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1792.p1804,GridMinus.atNode 1804,GridMinus.atNode 1805,NodeMinus28.w12,CompactMinus1792.checked1804,CompactMinus1792.small1804,CompactMinus1792.nodes1804,NodeMinus28.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1792.p1805,GridMinus.atNode 1805,GridMinus.atNode 1806,NodeMinus28.w13,CompactMinus1792.checked1805,CompactMinus1792.small1805,CompactMinus1792.nodes1805,NodeMinus28.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1792.p1806,GridMinus.atNode 1806,GridMinus.atNode 1807,NodeMinus28.w14,CompactMinus1792.checked1806,CompactMinus1792.small1806,CompactMinus1792.nodes1806,NodeMinus28.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1792.p1807,GridMinus.atNode 1807,GridMinus.atNode 1808,NodeMinus28.w15,CompactMinus1792.checked1807,CompactMinus1792.small1807,CompactMinus1792.nodes1807,NodeMinus28.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1808.p1808,GridMinus.atNode 1808,GridMinus.atNode 1809,NodeMinus28.w16,CompactMinus1808.checked1808,CompactMinus1808.small1808,CompactMinus1808.nodes1808,NodeMinus28.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1808.p1809,GridMinus.atNode 1809,GridMinus.atNode 1810,NodeMinus28.w17,CompactMinus1808.checked1809,CompactMinus1808.small1809,CompactMinus1808.nodes1809,NodeMinus28.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1808.p1810,GridMinus.atNode 1810,GridMinus.atNode 1811,NodeMinus28.w18,CompactMinus1808.checked1810,CompactMinus1808.small1810,CompactMinus1808.nodes1810,NodeMinus28.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1808.p1811,GridMinus.atNode 1811,GridMinus.atNode 1812,NodeMinus28.w19,CompactMinus1808.checked1811,CompactMinus1808.small1811,CompactMinus1808.nodes1811,NodeMinus28.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1808.p1812,GridMinus.atNode 1812,GridMinus.atNode 1813,NodeMinus28.w20,CompactMinus1808.checked1812,CompactMinus1808.small1812,CompactMinus1808.nodes1812,NodeMinus28.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1808.p1813,GridMinus.atNode 1813,GridMinus.atNode 1814,NodeMinus28.w21,CompactMinus1808.checked1813,CompactMinus1808.small1813,CompactMinus1808.nodes1813,NodeMinus28.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1808.p1814,GridMinus.atNode 1814,GridMinus.atNode 1815,NodeMinus28.w22,CompactMinus1808.checked1814,CompactMinus1808.small1814,CompactMinus1808.nodes1814,NodeMinus28.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1808.p1815,GridMinus.atNode 1815,GridMinus.atNode 1816,NodeMinus28.w23,CompactMinus1808.checked1815,CompactMinus1808.small1815,CompactMinus1808.nodes1815,NodeMinus28.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1808.p1816,GridMinus.atNode 1816,GridMinus.atNode 1817,NodeMinus28.w24,CompactMinus1808.checked1816,CompactMinus1808.small1816,CompactMinus1808.nodes1816,NodeMinus28.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1808.p1817,GridMinus.atNode 1817,GridMinus.atNode 1818,NodeMinus28.w25,CompactMinus1808.checked1817,CompactMinus1808.small1817,CompactMinus1808.nodes1817,NodeMinus28.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1808.p1818,GridMinus.atNode 1818,GridMinus.atNode 1819,NodeMinus28.w26,CompactMinus1808.checked1818,CompactMinus1808.small1818,CompactMinus1808.nodes1818,NodeMinus28.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1808.p1819,GridMinus.atNode 1819,GridMinus.atNode 1820,NodeMinus28.w27,CompactMinus1808.checked1819,CompactMinus1808.small1819,CompactMinus1808.nodes1819,NodeMinus28.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1808.p1820,GridMinus.atNode 1820,GridMinus.atNode 1821,NodeMinus28.w28,CompactMinus1808.checked1820,CompactMinus1808.small1820,CompactMinus1808.nodes1820,NodeMinus28.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1808.p1821,GridMinus.atNode 1821,GridMinus.atNode 1822,NodeMinus28.w29,CompactMinus1808.checked1821,CompactMinus1808.small1821,CompactMinus1808.nodes1821,NodeMinus28.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1808.p1822,GridMinus.atNode 1822,GridMinus.atNode 1823,NodeMinus28.w30,CompactMinus1808.checked1822,CompactMinus1808.small1822,CompactMinus1808.nodes1822,NodeMinus28.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1808.p1823,GridMinus.atNode 1823,GridMinus.atNode 1824,NodeMinus28.w31,CompactMinus1808.checked1823,CompactMinus1808.small1823,CompactMinus1808.nodes1823,NodeMinus28.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1824.p1824,GridMinus.atNode 1824,GridMinus.atNode 1825,NodeMinus28.w32,CompactMinus1824.checked1824,CompactMinus1824.small1824,CompactMinus1824.nodes1824,NodeMinus28.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1824.p1825,GridMinus.atNode 1825,GridMinus.atNode 1826,NodeMinus28.w33,CompactMinus1824.checked1825,CompactMinus1824.small1825,CompactMinus1824.nodes1825,NodeMinus28.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1824.p1826,GridMinus.atNode 1826,GridMinus.atNode 1827,NodeMinus28.w34,CompactMinus1824.checked1826,CompactMinus1824.small1826,CompactMinus1824.nodes1826,NodeMinus28.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1824.p1827,GridMinus.atNode 1827,GridMinus.atNode 1828,NodeMinus28.w35,CompactMinus1824.checked1827,CompactMinus1824.small1827,CompactMinus1824.nodes1827,NodeMinus28.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1824.p1828,GridMinus.atNode 1828,GridMinus.atNode 1829,NodeMinus28.w36,CompactMinus1824.checked1828,CompactMinus1824.small1828,CompactMinus1824.nodes1828,NodeMinus28.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1824.p1829,GridMinus.atNode 1829,GridMinus.atNode 1830,NodeMinus28.w37,CompactMinus1824.checked1829,CompactMinus1824.small1829,CompactMinus1824.nodes1829,NodeMinus28.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1824.p1830,GridMinus.atNode 1830,GridMinus.atNode 1831,NodeMinus28.w38,CompactMinus1824.checked1830,CompactMinus1824.small1830,CompactMinus1824.nodes1830,NodeMinus28.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1824.p1831,GridMinus.atNode 1831,GridMinus.atNode 1832,NodeMinus28.w39,CompactMinus1824.checked1831,CompactMinus1824.small1831,CompactMinus1824.nodes1831,NodeMinus28.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1824.p1832,GridMinus.atNode 1832,GridMinus.atNode 1833,NodeMinus28.w40,CompactMinus1824.checked1832,CompactMinus1824.small1832,CompactMinus1824.nodes1832,NodeMinus28.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1824.p1833,GridMinus.atNode 1833,GridMinus.atNode 1834,NodeMinus28.w41,CompactMinus1824.checked1833,CompactMinus1824.small1833,CompactMinus1824.nodes1833,NodeMinus28.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1824.p1834,GridMinus.atNode 1834,GridMinus.atNode 1835,NodeMinus28.w42,CompactMinus1824.checked1834,CompactMinus1824.small1834,CompactMinus1824.nodes1834,NodeMinus28.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1824.p1835,GridMinus.atNode 1835,GridMinus.atNode 1836,NodeMinus28.w43,CompactMinus1824.checked1835,CompactMinus1824.small1835,CompactMinus1824.nodes1835,NodeMinus28.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1824.p1836,GridMinus.atNode 1836,GridMinus.atNode 1837,NodeMinus28.w44,CompactMinus1824.checked1836,CompactMinus1824.small1836,CompactMinus1824.nodes1836,NodeMinus28.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1824.p1837,GridMinus.atNode 1837,GridMinus.atNode 1838,NodeMinus28.w45,CompactMinus1824.checked1837,CompactMinus1824.small1837,CompactMinus1824.nodes1837,NodeMinus28.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1824.p1838,GridMinus.atNode 1838,GridMinus.atNode 1839,NodeMinus28.w46,CompactMinus1824.checked1838,CompactMinus1824.small1838,CompactMinus1824.nodes1838,NodeMinus28.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1824.p1839,GridMinus.atNode 1839,GridMinus.atNode 1840,NodeMinus28.w47,CompactMinus1824.checked1839,CompactMinus1824.small1839,CompactMinus1824.nodes1839,NodeMinus28.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1840.p1840,GridMinus.atNode 1840,GridMinus.atNode 1841,NodeMinus28.w48,CompactMinus1840.checked1840,CompactMinus1840.small1840,CompactMinus1840.nodes1840,NodeMinus28.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1840.p1841,GridMinus.atNode 1841,GridMinus.atNode 1842,NodeMinus28.w49,CompactMinus1840.checked1841,CompactMinus1840.small1841,CompactMinus1840.nodes1841,NodeMinus28.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1840.p1842,GridMinus.atNode 1842,GridMinus.atNode 1843,NodeMinus28.w50,CompactMinus1840.checked1842,CompactMinus1840.small1842,CompactMinus1840.nodes1842,NodeMinus28.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1840.p1843,GridMinus.atNode 1843,GridMinus.atNode 1844,NodeMinus28.w51,CompactMinus1840.checked1843,CompactMinus1840.small1843,CompactMinus1840.nodes1843,NodeMinus28.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1840.p1844,GridMinus.atNode 1844,GridMinus.atNode 1845,NodeMinus28.w52,CompactMinus1840.checked1844,CompactMinus1840.small1844,CompactMinus1840.nodes1844,NodeMinus28.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1840.p1845,GridMinus.atNode 1845,GridMinus.atNode 1846,NodeMinus28.w53,CompactMinus1840.checked1845,CompactMinus1840.small1845,CompactMinus1840.nodes1845,NodeMinus28.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1840.p1846,GridMinus.atNode 1846,GridMinus.atNode 1847,NodeMinus28.w54,CompactMinus1840.checked1846,CompactMinus1840.small1846,CompactMinus1840.nodes1846,NodeMinus28.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1840.p1847,GridMinus.atNode 1847,GridMinus.atNode 1848,NodeMinus28.w55,CompactMinus1840.checked1847,CompactMinus1840.small1847,CompactMinus1840.nodes1847,NodeMinus28.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1840.p1848,GridMinus.atNode 1848,GridMinus.atNode 1849,NodeMinus28.w56,CompactMinus1840.checked1848,CompactMinus1840.small1848,CompactMinus1840.nodes1848,NodeMinus28.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1840.p1849,GridMinus.atNode 1849,GridMinus.atNode 1850,NodeMinus28.w57,CompactMinus1840.checked1849,CompactMinus1840.small1849,CompactMinus1840.nodes1849,NodeMinus28.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1840.p1850,GridMinus.atNode 1850,GridMinus.atNode 1851,NodeMinus28.w58,CompactMinus1840.checked1850,CompactMinus1840.small1850,CompactMinus1840.nodes1850,NodeMinus28.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1840.p1851,GridMinus.atNode 1851,GridMinus.atNode 1852,NodeMinus28.w59,CompactMinus1840.checked1851,CompactMinus1840.small1851,CompactMinus1840.nodes1851,NodeMinus28.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1840.p1852,GridMinus.atNode 1852,GridMinus.atNode 1853,NodeMinus28.w60,CompactMinus1840.checked1852,CompactMinus1840.small1852,CompactMinus1840.nodes1852,NodeMinus28.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1840.p1853,GridMinus.atNode 1853,GridMinus.atNode 1854,NodeMinus28.w61,CompactMinus1840.checked1853,CompactMinus1840.small1853,CompactMinus1840.nodes1853,NodeMinus28.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1840.p1854,GridMinus.atNode 1854,GridMinus.atNode 1855,NodeMinus28.w62,CompactMinus1840.checked1854,CompactMinus1840.small1854,CompactMinus1840.nodes1854,NodeMinus28.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1840.p1855,GridMinus.atNode 1855,GridMinus.atNode 1856,NodeMinus28.w63,CompactMinus1840.checked1855,CompactMinus1840.small1855,CompactMinus1840.nodes1855,NodeMinus28.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (1792+j) ∧
    (atRow j).right=GridMinus.atNode (1792+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus28
