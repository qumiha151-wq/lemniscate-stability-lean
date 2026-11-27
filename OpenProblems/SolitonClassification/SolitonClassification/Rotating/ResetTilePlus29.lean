import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus1856
import SolitonClassification.Rotating.ResetPackedPlus1872
import SolitonClassification.Rotating.ResetPackedPlus1888
import SolitonClassification.Rotating.ResetPackedPlus1904
namespace SolitonClassification.Rotating.DyadicReset.TilePlus29
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus1856.p1856,GridPlus.atNode 1856,GridPlus.atNode 1857,NodePlus29.w0,CompactPlus1856.checked1856,CompactPlus1856.small1856,CompactPlus1856.nodes1856,NodePlus29.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus1856.p1857,GridPlus.atNode 1857,GridPlus.atNode 1858,NodePlus29.w1,CompactPlus1856.checked1857,CompactPlus1856.small1857,CompactPlus1856.nodes1857,NodePlus29.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus1856.p1858,GridPlus.atNode 1858,GridPlus.atNode 1859,NodePlus29.w2,CompactPlus1856.checked1858,CompactPlus1856.small1858,CompactPlus1856.nodes1858,NodePlus29.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus1856.p1859,GridPlus.atNode 1859,GridPlus.atNode 1860,NodePlus29.w3,CompactPlus1856.checked1859,CompactPlus1856.small1859,CompactPlus1856.nodes1859,NodePlus29.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus1856.p1860,GridPlus.atNode 1860,GridPlus.atNode 1861,NodePlus29.w4,CompactPlus1856.checked1860,CompactPlus1856.small1860,CompactPlus1856.nodes1860,NodePlus29.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus1856.p1861,GridPlus.atNode 1861,GridPlus.atNode 1862,NodePlus29.w5,CompactPlus1856.checked1861,CompactPlus1856.small1861,CompactPlus1856.nodes1861,NodePlus29.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus1856.p1862,GridPlus.atNode 1862,GridPlus.atNode 1863,NodePlus29.w6,CompactPlus1856.checked1862,CompactPlus1856.small1862,CompactPlus1856.nodes1862,NodePlus29.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus1856.p1863,GridPlus.atNode 1863,GridPlus.atNode 1864,NodePlus29.w7,CompactPlus1856.checked1863,CompactPlus1856.small1863,CompactPlus1856.nodes1863,NodePlus29.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus1856.p1864,GridPlus.atNode 1864,GridPlus.atNode 1865,NodePlus29.w8,CompactPlus1856.checked1864,CompactPlus1856.small1864,CompactPlus1856.nodes1864,NodePlus29.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus1856.p1865,GridPlus.atNode 1865,GridPlus.atNode 1866,NodePlus29.w9,CompactPlus1856.checked1865,CompactPlus1856.small1865,CompactPlus1856.nodes1865,NodePlus29.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus1856.p1866,GridPlus.atNode 1866,GridPlus.atNode 1867,NodePlus29.w10,CompactPlus1856.checked1866,CompactPlus1856.small1866,CompactPlus1856.nodes1866,NodePlus29.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus1856.p1867,GridPlus.atNode 1867,GridPlus.atNode 1868,NodePlus29.w11,CompactPlus1856.checked1867,CompactPlus1856.small1867,CompactPlus1856.nodes1867,NodePlus29.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus1856.p1868,GridPlus.atNode 1868,GridPlus.atNode 1869,NodePlus29.w12,CompactPlus1856.checked1868,CompactPlus1856.small1868,CompactPlus1856.nodes1868,NodePlus29.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus1856.p1869,GridPlus.atNode 1869,GridPlus.atNode 1870,NodePlus29.w13,CompactPlus1856.checked1869,CompactPlus1856.small1869,CompactPlus1856.nodes1869,NodePlus29.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus1856.p1870,GridPlus.atNode 1870,GridPlus.atNode 1871,NodePlus29.w14,CompactPlus1856.checked1870,CompactPlus1856.small1870,CompactPlus1856.nodes1870,NodePlus29.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus1856.p1871,GridPlus.atNode 1871,GridPlus.atNode 1872,NodePlus29.w15,CompactPlus1856.checked1871,CompactPlus1856.small1871,CompactPlus1856.nodes1871,NodePlus29.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus1872.p1872,GridPlus.atNode 1872,GridPlus.atNode 1873,NodePlus29.w16,CompactPlus1872.checked1872,CompactPlus1872.small1872,CompactPlus1872.nodes1872,NodePlus29.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus1872.p1873,GridPlus.atNode 1873,GridPlus.atNode 1874,NodePlus29.w17,CompactPlus1872.checked1873,CompactPlus1872.small1873,CompactPlus1872.nodes1873,NodePlus29.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus1872.p1874,GridPlus.atNode 1874,GridPlus.atNode 1875,NodePlus29.w18,CompactPlus1872.checked1874,CompactPlus1872.small1874,CompactPlus1872.nodes1874,NodePlus29.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus1872.p1875,GridPlus.atNode 1875,GridPlus.atNode 1876,NodePlus29.w19,CompactPlus1872.checked1875,CompactPlus1872.small1875,CompactPlus1872.nodes1875,NodePlus29.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus1872.p1876,GridPlus.atNode 1876,GridPlus.atNode 1877,NodePlus29.w20,CompactPlus1872.checked1876,CompactPlus1872.small1876,CompactPlus1872.nodes1876,NodePlus29.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus1872.p1877,GridPlus.atNode 1877,GridPlus.atNode 1878,NodePlus29.w21,CompactPlus1872.checked1877,CompactPlus1872.small1877,CompactPlus1872.nodes1877,NodePlus29.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus1872.p1878,GridPlus.atNode 1878,GridPlus.atNode 1879,NodePlus29.w22,CompactPlus1872.checked1878,CompactPlus1872.small1878,CompactPlus1872.nodes1878,NodePlus29.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus1872.p1879,GridPlus.atNode 1879,GridPlus.atNode 1880,NodePlus29.w23,CompactPlus1872.checked1879,CompactPlus1872.small1879,CompactPlus1872.nodes1879,NodePlus29.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus1872.p1880,GridPlus.atNode 1880,GridPlus.atNode 1881,NodePlus29.w24,CompactPlus1872.checked1880,CompactPlus1872.small1880,CompactPlus1872.nodes1880,NodePlus29.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus1872.p1881,GridPlus.atNode 1881,GridPlus.atNode 1882,NodePlus29.w25,CompactPlus1872.checked1881,CompactPlus1872.small1881,CompactPlus1872.nodes1881,NodePlus29.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus1872.p1882,GridPlus.atNode 1882,GridPlus.atNode 1883,NodePlus29.w26,CompactPlus1872.checked1882,CompactPlus1872.small1882,CompactPlus1872.nodes1882,NodePlus29.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus1872.p1883,GridPlus.atNode 1883,GridPlus.atNode 1884,NodePlus29.w27,CompactPlus1872.checked1883,CompactPlus1872.small1883,CompactPlus1872.nodes1883,NodePlus29.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus1872.p1884,GridPlus.atNode 1884,GridPlus.atNode 1885,NodePlus29.w28,CompactPlus1872.checked1884,CompactPlus1872.small1884,CompactPlus1872.nodes1884,NodePlus29.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus1872.p1885,GridPlus.atNode 1885,GridPlus.atNode 1886,NodePlus29.w29,CompactPlus1872.checked1885,CompactPlus1872.small1885,CompactPlus1872.nodes1885,NodePlus29.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus1872.p1886,GridPlus.atNode 1886,GridPlus.atNode 1887,NodePlus29.w30,CompactPlus1872.checked1886,CompactPlus1872.small1886,CompactPlus1872.nodes1886,NodePlus29.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus1872.p1887,GridPlus.atNode 1887,GridPlus.atNode 1888,NodePlus29.w31,CompactPlus1872.checked1887,CompactPlus1872.small1887,CompactPlus1872.nodes1887,NodePlus29.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus1888.p1888,GridPlus.atNode 1888,GridPlus.atNode 1889,NodePlus29.w32,CompactPlus1888.checked1888,CompactPlus1888.small1888,CompactPlus1888.nodes1888,NodePlus29.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus1888.p1889,GridPlus.atNode 1889,GridPlus.atNode 1890,NodePlus29.w33,CompactPlus1888.checked1889,CompactPlus1888.small1889,CompactPlus1888.nodes1889,NodePlus29.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus1888.p1890,GridPlus.atNode 1890,GridPlus.atNode 1891,NodePlus29.w34,CompactPlus1888.checked1890,CompactPlus1888.small1890,CompactPlus1888.nodes1890,NodePlus29.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus1888.p1891,GridPlus.atNode 1891,GridPlus.atNode 1892,NodePlus29.w35,CompactPlus1888.checked1891,CompactPlus1888.small1891,CompactPlus1888.nodes1891,NodePlus29.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus1888.p1892,GridPlus.atNode 1892,GridPlus.atNode 1893,NodePlus29.w36,CompactPlus1888.checked1892,CompactPlus1888.small1892,CompactPlus1888.nodes1892,NodePlus29.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus1888.p1893,GridPlus.atNode 1893,GridPlus.atNode 1894,NodePlus29.w37,CompactPlus1888.checked1893,CompactPlus1888.small1893,CompactPlus1888.nodes1893,NodePlus29.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus1888.p1894,GridPlus.atNode 1894,GridPlus.atNode 1895,NodePlus29.w38,CompactPlus1888.checked1894,CompactPlus1888.small1894,CompactPlus1888.nodes1894,NodePlus29.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus1888.p1895,GridPlus.atNode 1895,GridPlus.atNode 1896,NodePlus29.w39,CompactPlus1888.checked1895,CompactPlus1888.small1895,CompactPlus1888.nodes1895,NodePlus29.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus1888.p1896,GridPlus.atNode 1896,GridPlus.atNode 1897,NodePlus29.w40,CompactPlus1888.checked1896,CompactPlus1888.small1896,CompactPlus1888.nodes1896,NodePlus29.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus1888.p1897,GridPlus.atNode 1897,GridPlus.atNode 1898,NodePlus29.w41,CompactPlus1888.checked1897,CompactPlus1888.small1897,CompactPlus1888.nodes1897,NodePlus29.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus1888.p1898,GridPlus.atNode 1898,GridPlus.atNode 1899,NodePlus29.w42,CompactPlus1888.checked1898,CompactPlus1888.small1898,CompactPlus1888.nodes1898,NodePlus29.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus1888.p1899,GridPlus.atNode 1899,GridPlus.atNode 1900,NodePlus29.w43,CompactPlus1888.checked1899,CompactPlus1888.small1899,CompactPlus1888.nodes1899,NodePlus29.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus1888.p1900,GridPlus.atNode 1900,GridPlus.atNode 1901,NodePlus29.w44,CompactPlus1888.checked1900,CompactPlus1888.small1900,CompactPlus1888.nodes1900,NodePlus29.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus1888.p1901,GridPlus.atNode 1901,GridPlus.atNode 1902,NodePlus29.w45,CompactPlus1888.checked1901,CompactPlus1888.small1901,CompactPlus1888.nodes1901,NodePlus29.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus1888.p1902,GridPlus.atNode 1902,GridPlus.atNode 1903,NodePlus29.w46,CompactPlus1888.checked1902,CompactPlus1888.small1902,CompactPlus1888.nodes1902,NodePlus29.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus1888.p1903,GridPlus.atNode 1903,GridPlus.atNode 1904,NodePlus29.w47,CompactPlus1888.checked1903,CompactPlus1888.small1903,CompactPlus1888.nodes1903,NodePlus29.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus1904.p1904,GridPlus.atNode 1904,GridPlus.atNode 1905,NodePlus29.w48,CompactPlus1904.checked1904,CompactPlus1904.small1904,CompactPlus1904.nodes1904,NodePlus29.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus1904.p1905,GridPlus.atNode 1905,GridPlus.atNode 1906,NodePlus29.w49,CompactPlus1904.checked1905,CompactPlus1904.small1905,CompactPlus1904.nodes1905,NodePlus29.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus1904.p1906,GridPlus.atNode 1906,GridPlus.atNode 1907,NodePlus29.w50,CompactPlus1904.checked1906,CompactPlus1904.small1906,CompactPlus1904.nodes1906,NodePlus29.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus1904.p1907,GridPlus.atNode 1907,GridPlus.atNode 1908,NodePlus29.w51,CompactPlus1904.checked1907,CompactPlus1904.small1907,CompactPlus1904.nodes1907,NodePlus29.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus1904.p1908,GridPlus.atNode 1908,GridPlus.atNode 1909,NodePlus29.w52,CompactPlus1904.checked1908,CompactPlus1904.small1908,CompactPlus1904.nodes1908,NodePlus29.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus1904.p1909,GridPlus.atNode 1909,GridPlus.atNode 1910,NodePlus29.w53,CompactPlus1904.checked1909,CompactPlus1904.small1909,CompactPlus1904.nodes1909,NodePlus29.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus1904.p1910,GridPlus.atNode 1910,GridPlus.atNode 1911,NodePlus29.w54,CompactPlus1904.checked1910,CompactPlus1904.small1910,CompactPlus1904.nodes1910,NodePlus29.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus1904.p1911,GridPlus.atNode 1911,GridPlus.atNode 1912,NodePlus29.w55,CompactPlus1904.checked1911,CompactPlus1904.small1911,CompactPlus1904.nodes1911,NodePlus29.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus1904.p1912,GridPlus.atNode 1912,GridPlus.atNode 1913,NodePlus29.w56,CompactPlus1904.checked1912,CompactPlus1904.small1912,CompactPlus1904.nodes1912,NodePlus29.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus1904.p1913,GridPlus.atNode 1913,GridPlus.atNode 1914,NodePlus29.w57,CompactPlus1904.checked1913,CompactPlus1904.small1913,CompactPlus1904.nodes1913,NodePlus29.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus1904.p1914,GridPlus.atNode 1914,GridPlus.atNode 1915,NodePlus29.w58,CompactPlus1904.checked1914,CompactPlus1904.small1914,CompactPlus1904.nodes1914,NodePlus29.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus1904.p1915,GridPlus.atNode 1915,GridPlus.atNode 1916,NodePlus29.w59,CompactPlus1904.checked1915,CompactPlus1904.small1915,CompactPlus1904.nodes1915,NodePlus29.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus1904.p1916,GridPlus.atNode 1916,GridPlus.atNode 1917,NodePlus29.w60,CompactPlus1904.checked1916,CompactPlus1904.small1916,CompactPlus1904.nodes1916,NodePlus29.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus1904.p1917,GridPlus.atNode 1917,GridPlus.atNode 1918,NodePlus29.w61,CompactPlus1904.checked1917,CompactPlus1904.small1917,CompactPlus1904.nodes1917,NodePlus29.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus1904.p1918,GridPlus.atNode 1918,GridPlus.atNode 1919,NodePlus29.w62,CompactPlus1904.checked1918,CompactPlus1904.small1918,CompactPlus1904.nodes1918,NodePlus29.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus1904.p1919,GridPlus.atNode 1919,GridPlus.atNode 1920,NodePlus29.w63,CompactPlus1904.checked1919,CompactPlus1904.small1919,CompactPlus1904.nodes1919,NodePlus29.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (1856+j) ∧
    (atRow j).right=GridPlus.atNode (1856+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus29
