import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus1856
import SolitonClassification.Rotating.ResetPackedMinus1872
import SolitonClassification.Rotating.ResetPackedMinus1888
import SolitonClassification.Rotating.ResetPackedMinus1904
namespace SolitonClassification.Rotating.DyadicReset.TileMinus29
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1856.p1856,GridMinus.atNode 1856,GridMinus.atNode 1857,NodeMinus29.w0,CompactMinus1856.checked1856,CompactMinus1856.small1856,CompactMinus1856.nodes1856,NodeMinus29.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1856.p1857,GridMinus.atNode 1857,GridMinus.atNode 1858,NodeMinus29.w1,CompactMinus1856.checked1857,CompactMinus1856.small1857,CompactMinus1856.nodes1857,NodeMinus29.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1856.p1858,GridMinus.atNode 1858,GridMinus.atNode 1859,NodeMinus29.w2,CompactMinus1856.checked1858,CompactMinus1856.small1858,CompactMinus1856.nodes1858,NodeMinus29.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1856.p1859,GridMinus.atNode 1859,GridMinus.atNode 1860,NodeMinus29.w3,CompactMinus1856.checked1859,CompactMinus1856.small1859,CompactMinus1856.nodes1859,NodeMinus29.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1856.p1860,GridMinus.atNode 1860,GridMinus.atNode 1861,NodeMinus29.w4,CompactMinus1856.checked1860,CompactMinus1856.small1860,CompactMinus1856.nodes1860,NodeMinus29.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1856.p1861,GridMinus.atNode 1861,GridMinus.atNode 1862,NodeMinus29.w5,CompactMinus1856.checked1861,CompactMinus1856.small1861,CompactMinus1856.nodes1861,NodeMinus29.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1856.p1862,GridMinus.atNode 1862,GridMinus.atNode 1863,NodeMinus29.w6,CompactMinus1856.checked1862,CompactMinus1856.small1862,CompactMinus1856.nodes1862,NodeMinus29.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1856.p1863,GridMinus.atNode 1863,GridMinus.atNode 1864,NodeMinus29.w7,CompactMinus1856.checked1863,CompactMinus1856.small1863,CompactMinus1856.nodes1863,NodeMinus29.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1856.p1864,GridMinus.atNode 1864,GridMinus.atNode 1865,NodeMinus29.w8,CompactMinus1856.checked1864,CompactMinus1856.small1864,CompactMinus1856.nodes1864,NodeMinus29.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1856.p1865,GridMinus.atNode 1865,GridMinus.atNode 1866,NodeMinus29.w9,CompactMinus1856.checked1865,CompactMinus1856.small1865,CompactMinus1856.nodes1865,NodeMinus29.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1856.p1866,GridMinus.atNode 1866,GridMinus.atNode 1867,NodeMinus29.w10,CompactMinus1856.checked1866,CompactMinus1856.small1866,CompactMinus1856.nodes1866,NodeMinus29.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1856.p1867,GridMinus.atNode 1867,GridMinus.atNode 1868,NodeMinus29.w11,CompactMinus1856.checked1867,CompactMinus1856.small1867,CompactMinus1856.nodes1867,NodeMinus29.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1856.p1868,GridMinus.atNode 1868,GridMinus.atNode 1869,NodeMinus29.w12,CompactMinus1856.checked1868,CompactMinus1856.small1868,CompactMinus1856.nodes1868,NodeMinus29.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1856.p1869,GridMinus.atNode 1869,GridMinus.atNode 1870,NodeMinus29.w13,CompactMinus1856.checked1869,CompactMinus1856.small1869,CompactMinus1856.nodes1869,NodeMinus29.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1856.p1870,GridMinus.atNode 1870,GridMinus.atNode 1871,NodeMinus29.w14,CompactMinus1856.checked1870,CompactMinus1856.small1870,CompactMinus1856.nodes1870,NodeMinus29.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1856.p1871,GridMinus.atNode 1871,GridMinus.atNode 1872,NodeMinus29.w15,CompactMinus1856.checked1871,CompactMinus1856.small1871,CompactMinus1856.nodes1871,NodeMinus29.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1872.p1872,GridMinus.atNode 1872,GridMinus.atNode 1873,NodeMinus29.w16,CompactMinus1872.checked1872,CompactMinus1872.small1872,CompactMinus1872.nodes1872,NodeMinus29.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1872.p1873,GridMinus.atNode 1873,GridMinus.atNode 1874,NodeMinus29.w17,CompactMinus1872.checked1873,CompactMinus1872.small1873,CompactMinus1872.nodes1873,NodeMinus29.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1872.p1874,GridMinus.atNode 1874,GridMinus.atNode 1875,NodeMinus29.w18,CompactMinus1872.checked1874,CompactMinus1872.small1874,CompactMinus1872.nodes1874,NodeMinus29.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1872.p1875,GridMinus.atNode 1875,GridMinus.atNode 1876,NodeMinus29.w19,CompactMinus1872.checked1875,CompactMinus1872.small1875,CompactMinus1872.nodes1875,NodeMinus29.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1872.p1876,GridMinus.atNode 1876,GridMinus.atNode 1877,NodeMinus29.w20,CompactMinus1872.checked1876,CompactMinus1872.small1876,CompactMinus1872.nodes1876,NodeMinus29.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1872.p1877,GridMinus.atNode 1877,GridMinus.atNode 1878,NodeMinus29.w21,CompactMinus1872.checked1877,CompactMinus1872.small1877,CompactMinus1872.nodes1877,NodeMinus29.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1872.p1878,GridMinus.atNode 1878,GridMinus.atNode 1879,NodeMinus29.w22,CompactMinus1872.checked1878,CompactMinus1872.small1878,CompactMinus1872.nodes1878,NodeMinus29.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1872.p1879,GridMinus.atNode 1879,GridMinus.atNode 1880,NodeMinus29.w23,CompactMinus1872.checked1879,CompactMinus1872.small1879,CompactMinus1872.nodes1879,NodeMinus29.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1872.p1880,GridMinus.atNode 1880,GridMinus.atNode 1881,NodeMinus29.w24,CompactMinus1872.checked1880,CompactMinus1872.small1880,CompactMinus1872.nodes1880,NodeMinus29.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1872.p1881,GridMinus.atNode 1881,GridMinus.atNode 1882,NodeMinus29.w25,CompactMinus1872.checked1881,CompactMinus1872.small1881,CompactMinus1872.nodes1881,NodeMinus29.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1872.p1882,GridMinus.atNode 1882,GridMinus.atNode 1883,NodeMinus29.w26,CompactMinus1872.checked1882,CompactMinus1872.small1882,CompactMinus1872.nodes1882,NodeMinus29.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1872.p1883,GridMinus.atNode 1883,GridMinus.atNode 1884,NodeMinus29.w27,CompactMinus1872.checked1883,CompactMinus1872.small1883,CompactMinus1872.nodes1883,NodeMinus29.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1872.p1884,GridMinus.atNode 1884,GridMinus.atNode 1885,NodeMinus29.w28,CompactMinus1872.checked1884,CompactMinus1872.small1884,CompactMinus1872.nodes1884,NodeMinus29.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1872.p1885,GridMinus.atNode 1885,GridMinus.atNode 1886,NodeMinus29.w29,CompactMinus1872.checked1885,CompactMinus1872.small1885,CompactMinus1872.nodes1885,NodeMinus29.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1872.p1886,GridMinus.atNode 1886,GridMinus.atNode 1887,NodeMinus29.w30,CompactMinus1872.checked1886,CompactMinus1872.small1886,CompactMinus1872.nodes1886,NodeMinus29.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1872.p1887,GridMinus.atNode 1887,GridMinus.atNode 1888,NodeMinus29.w31,CompactMinus1872.checked1887,CompactMinus1872.small1887,CompactMinus1872.nodes1887,NodeMinus29.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1888.p1888,GridMinus.atNode 1888,GridMinus.atNode 1889,NodeMinus29.w32,CompactMinus1888.checked1888,CompactMinus1888.small1888,CompactMinus1888.nodes1888,NodeMinus29.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1888.p1889,GridMinus.atNode 1889,GridMinus.atNode 1890,NodeMinus29.w33,CompactMinus1888.checked1889,CompactMinus1888.small1889,CompactMinus1888.nodes1889,NodeMinus29.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1888.p1890,GridMinus.atNode 1890,GridMinus.atNode 1891,NodeMinus29.w34,CompactMinus1888.checked1890,CompactMinus1888.small1890,CompactMinus1888.nodes1890,NodeMinus29.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1888.p1891,GridMinus.atNode 1891,GridMinus.atNode 1892,NodeMinus29.w35,CompactMinus1888.checked1891,CompactMinus1888.small1891,CompactMinus1888.nodes1891,NodeMinus29.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1888.p1892,GridMinus.atNode 1892,GridMinus.atNode 1893,NodeMinus29.w36,CompactMinus1888.checked1892,CompactMinus1888.small1892,CompactMinus1888.nodes1892,NodeMinus29.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1888.p1893,GridMinus.atNode 1893,GridMinus.atNode 1894,NodeMinus29.w37,CompactMinus1888.checked1893,CompactMinus1888.small1893,CompactMinus1888.nodes1893,NodeMinus29.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1888.p1894,GridMinus.atNode 1894,GridMinus.atNode 1895,NodeMinus29.w38,CompactMinus1888.checked1894,CompactMinus1888.small1894,CompactMinus1888.nodes1894,NodeMinus29.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1888.p1895,GridMinus.atNode 1895,GridMinus.atNode 1896,NodeMinus29.w39,CompactMinus1888.checked1895,CompactMinus1888.small1895,CompactMinus1888.nodes1895,NodeMinus29.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1888.p1896,GridMinus.atNode 1896,GridMinus.atNode 1897,NodeMinus29.w40,CompactMinus1888.checked1896,CompactMinus1888.small1896,CompactMinus1888.nodes1896,NodeMinus29.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1888.p1897,GridMinus.atNode 1897,GridMinus.atNode 1898,NodeMinus29.w41,CompactMinus1888.checked1897,CompactMinus1888.small1897,CompactMinus1888.nodes1897,NodeMinus29.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1888.p1898,GridMinus.atNode 1898,GridMinus.atNode 1899,NodeMinus29.w42,CompactMinus1888.checked1898,CompactMinus1888.small1898,CompactMinus1888.nodes1898,NodeMinus29.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1888.p1899,GridMinus.atNode 1899,GridMinus.atNode 1900,NodeMinus29.w43,CompactMinus1888.checked1899,CompactMinus1888.small1899,CompactMinus1888.nodes1899,NodeMinus29.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1888.p1900,GridMinus.atNode 1900,GridMinus.atNode 1901,NodeMinus29.w44,CompactMinus1888.checked1900,CompactMinus1888.small1900,CompactMinus1888.nodes1900,NodeMinus29.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1888.p1901,GridMinus.atNode 1901,GridMinus.atNode 1902,NodeMinus29.w45,CompactMinus1888.checked1901,CompactMinus1888.small1901,CompactMinus1888.nodes1901,NodeMinus29.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1888.p1902,GridMinus.atNode 1902,GridMinus.atNode 1903,NodeMinus29.w46,CompactMinus1888.checked1902,CompactMinus1888.small1902,CompactMinus1888.nodes1902,NodeMinus29.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1888.p1903,GridMinus.atNode 1903,GridMinus.atNode 1904,NodeMinus29.w47,CompactMinus1888.checked1903,CompactMinus1888.small1903,CompactMinus1888.nodes1903,NodeMinus29.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1904.p1904,GridMinus.atNode 1904,GridMinus.atNode 1905,NodeMinus29.w48,CompactMinus1904.checked1904,CompactMinus1904.small1904,CompactMinus1904.nodes1904,NodeMinus29.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1904.p1905,GridMinus.atNode 1905,GridMinus.atNode 1906,NodeMinus29.w49,CompactMinus1904.checked1905,CompactMinus1904.small1905,CompactMinus1904.nodes1905,NodeMinus29.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1904.p1906,GridMinus.atNode 1906,GridMinus.atNode 1907,NodeMinus29.w50,CompactMinus1904.checked1906,CompactMinus1904.small1906,CompactMinus1904.nodes1906,NodeMinus29.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1904.p1907,GridMinus.atNode 1907,GridMinus.atNode 1908,NodeMinus29.w51,CompactMinus1904.checked1907,CompactMinus1904.small1907,CompactMinus1904.nodes1907,NodeMinus29.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1904.p1908,GridMinus.atNode 1908,GridMinus.atNode 1909,NodeMinus29.w52,CompactMinus1904.checked1908,CompactMinus1904.small1908,CompactMinus1904.nodes1908,NodeMinus29.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1904.p1909,GridMinus.atNode 1909,GridMinus.atNode 1910,NodeMinus29.w53,CompactMinus1904.checked1909,CompactMinus1904.small1909,CompactMinus1904.nodes1909,NodeMinus29.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1904.p1910,GridMinus.atNode 1910,GridMinus.atNode 1911,NodeMinus29.w54,CompactMinus1904.checked1910,CompactMinus1904.small1910,CompactMinus1904.nodes1910,NodeMinus29.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1904.p1911,GridMinus.atNode 1911,GridMinus.atNode 1912,NodeMinus29.w55,CompactMinus1904.checked1911,CompactMinus1904.small1911,CompactMinus1904.nodes1911,NodeMinus29.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1904.p1912,GridMinus.atNode 1912,GridMinus.atNode 1913,NodeMinus29.w56,CompactMinus1904.checked1912,CompactMinus1904.small1912,CompactMinus1904.nodes1912,NodeMinus29.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1904.p1913,GridMinus.atNode 1913,GridMinus.atNode 1914,NodeMinus29.w57,CompactMinus1904.checked1913,CompactMinus1904.small1913,CompactMinus1904.nodes1913,NodeMinus29.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1904.p1914,GridMinus.atNode 1914,GridMinus.atNode 1915,NodeMinus29.w58,CompactMinus1904.checked1914,CompactMinus1904.small1914,CompactMinus1904.nodes1914,NodeMinus29.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1904.p1915,GridMinus.atNode 1915,GridMinus.atNode 1916,NodeMinus29.w59,CompactMinus1904.checked1915,CompactMinus1904.small1915,CompactMinus1904.nodes1915,NodeMinus29.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1904.p1916,GridMinus.atNode 1916,GridMinus.atNode 1917,NodeMinus29.w60,CompactMinus1904.checked1916,CompactMinus1904.small1916,CompactMinus1904.nodes1916,NodeMinus29.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1904.p1917,GridMinus.atNode 1917,GridMinus.atNode 1918,NodeMinus29.w61,CompactMinus1904.checked1917,CompactMinus1904.small1917,CompactMinus1904.nodes1917,NodeMinus29.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1904.p1918,GridMinus.atNode 1918,GridMinus.atNode 1919,NodeMinus29.w62,CompactMinus1904.checked1918,CompactMinus1904.small1918,CompactMinus1904.nodes1918,NodeMinus29.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1904.p1919,GridMinus.atNode 1919,GridMinus.atNode 1920,NodeMinus29.w63,CompactMinus1904.checked1919,CompactMinus1904.small1919,CompactMinus1904.nodes1919,NodeMinus29.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (1856+j) ∧
    (atRow j).right=GridMinus.atNode (1856+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus29
