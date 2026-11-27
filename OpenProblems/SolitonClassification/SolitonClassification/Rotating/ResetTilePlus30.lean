import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus1920
import SolitonClassification.Rotating.ResetPackedPlus1936
import SolitonClassification.Rotating.ResetPackedPlus1952
import SolitonClassification.Rotating.ResetPackedPlus1968
namespace SolitonClassification.Rotating.DyadicReset.TilePlus30
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus1920.p1920,GridPlus.atNode 1920,GridPlus.atNode 1921,NodePlus30.w0,CompactPlus1920.checked1920,CompactPlus1920.small1920,CompactPlus1920.nodes1920,NodePlus30.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus1920.p1921,GridPlus.atNode 1921,GridPlus.atNode 1922,NodePlus30.w1,CompactPlus1920.checked1921,CompactPlus1920.small1921,CompactPlus1920.nodes1921,NodePlus30.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus1920.p1922,GridPlus.atNode 1922,GridPlus.atNode 1923,NodePlus30.w2,CompactPlus1920.checked1922,CompactPlus1920.small1922,CompactPlus1920.nodes1922,NodePlus30.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus1920.p1923,GridPlus.atNode 1923,GridPlus.atNode 1924,NodePlus30.w3,CompactPlus1920.checked1923,CompactPlus1920.small1923,CompactPlus1920.nodes1923,NodePlus30.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus1920.p1924,GridPlus.atNode 1924,GridPlus.atNode 1925,NodePlus30.w4,CompactPlus1920.checked1924,CompactPlus1920.small1924,CompactPlus1920.nodes1924,NodePlus30.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus1920.p1925,GridPlus.atNode 1925,GridPlus.atNode 1926,NodePlus30.w5,CompactPlus1920.checked1925,CompactPlus1920.small1925,CompactPlus1920.nodes1925,NodePlus30.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus1920.p1926,GridPlus.atNode 1926,GridPlus.atNode 1927,NodePlus30.w6,CompactPlus1920.checked1926,CompactPlus1920.small1926,CompactPlus1920.nodes1926,NodePlus30.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus1920.p1927,GridPlus.atNode 1927,GridPlus.atNode 1928,NodePlus30.w7,CompactPlus1920.checked1927,CompactPlus1920.small1927,CompactPlus1920.nodes1927,NodePlus30.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus1920.p1928,GridPlus.atNode 1928,GridPlus.atNode 1929,NodePlus30.w8,CompactPlus1920.checked1928,CompactPlus1920.small1928,CompactPlus1920.nodes1928,NodePlus30.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus1920.p1929,GridPlus.atNode 1929,GridPlus.atNode 1930,NodePlus30.w9,CompactPlus1920.checked1929,CompactPlus1920.small1929,CompactPlus1920.nodes1929,NodePlus30.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus1920.p1930,GridPlus.atNode 1930,GridPlus.atNode 1931,NodePlus30.w10,CompactPlus1920.checked1930,CompactPlus1920.small1930,CompactPlus1920.nodes1930,NodePlus30.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus1920.p1931,GridPlus.atNode 1931,GridPlus.atNode 1932,NodePlus30.w11,CompactPlus1920.checked1931,CompactPlus1920.small1931,CompactPlus1920.nodes1931,NodePlus30.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus1920.p1932,GridPlus.atNode 1932,GridPlus.atNode 1933,NodePlus30.w12,CompactPlus1920.checked1932,CompactPlus1920.small1932,CompactPlus1920.nodes1932,NodePlus30.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus1920.p1933,GridPlus.atNode 1933,GridPlus.atNode 1934,NodePlus30.w13,CompactPlus1920.checked1933,CompactPlus1920.small1933,CompactPlus1920.nodes1933,NodePlus30.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus1920.p1934,GridPlus.atNode 1934,GridPlus.atNode 1935,NodePlus30.w14,CompactPlus1920.checked1934,CompactPlus1920.small1934,CompactPlus1920.nodes1934,NodePlus30.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus1920.p1935,GridPlus.atNode 1935,GridPlus.atNode 1936,NodePlus30.w15,CompactPlus1920.checked1935,CompactPlus1920.small1935,CompactPlus1920.nodes1935,NodePlus30.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus1936.p1936,GridPlus.atNode 1936,GridPlus.atNode 1937,NodePlus30.w16,CompactPlus1936.checked1936,CompactPlus1936.small1936,CompactPlus1936.nodes1936,NodePlus30.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus1936.p1937,GridPlus.atNode 1937,GridPlus.atNode 1938,NodePlus30.w17,CompactPlus1936.checked1937,CompactPlus1936.small1937,CompactPlus1936.nodes1937,NodePlus30.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus1936.p1938,GridPlus.atNode 1938,GridPlus.atNode 1939,NodePlus30.w18,CompactPlus1936.checked1938,CompactPlus1936.small1938,CompactPlus1936.nodes1938,NodePlus30.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus1936.p1939,GridPlus.atNode 1939,GridPlus.atNode 1940,NodePlus30.w19,CompactPlus1936.checked1939,CompactPlus1936.small1939,CompactPlus1936.nodes1939,NodePlus30.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus1936.p1940,GridPlus.atNode 1940,GridPlus.atNode 1941,NodePlus30.w20,CompactPlus1936.checked1940,CompactPlus1936.small1940,CompactPlus1936.nodes1940,NodePlus30.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus1936.p1941,GridPlus.atNode 1941,GridPlus.atNode 1942,NodePlus30.w21,CompactPlus1936.checked1941,CompactPlus1936.small1941,CompactPlus1936.nodes1941,NodePlus30.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus1936.p1942,GridPlus.atNode 1942,GridPlus.atNode 1943,NodePlus30.w22,CompactPlus1936.checked1942,CompactPlus1936.small1942,CompactPlus1936.nodes1942,NodePlus30.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus1936.p1943,GridPlus.atNode 1943,GridPlus.atNode 1944,NodePlus30.w23,CompactPlus1936.checked1943,CompactPlus1936.small1943,CompactPlus1936.nodes1943,NodePlus30.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus1936.p1944,GridPlus.atNode 1944,GridPlus.atNode 1945,NodePlus30.w24,CompactPlus1936.checked1944,CompactPlus1936.small1944,CompactPlus1936.nodes1944,NodePlus30.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus1936.p1945,GridPlus.atNode 1945,GridPlus.atNode 1946,NodePlus30.w25,CompactPlus1936.checked1945,CompactPlus1936.small1945,CompactPlus1936.nodes1945,NodePlus30.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus1936.p1946,GridPlus.atNode 1946,GridPlus.atNode 1947,NodePlus30.w26,CompactPlus1936.checked1946,CompactPlus1936.small1946,CompactPlus1936.nodes1946,NodePlus30.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus1936.p1947,GridPlus.atNode 1947,GridPlus.atNode 1948,NodePlus30.w27,CompactPlus1936.checked1947,CompactPlus1936.small1947,CompactPlus1936.nodes1947,NodePlus30.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus1936.p1948,GridPlus.atNode 1948,GridPlus.atNode 1949,NodePlus30.w28,CompactPlus1936.checked1948,CompactPlus1936.small1948,CompactPlus1936.nodes1948,NodePlus30.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus1936.p1949,GridPlus.atNode 1949,GridPlus.atNode 1950,NodePlus30.w29,CompactPlus1936.checked1949,CompactPlus1936.small1949,CompactPlus1936.nodes1949,NodePlus30.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus1936.p1950,GridPlus.atNode 1950,GridPlus.atNode 1951,NodePlus30.w30,CompactPlus1936.checked1950,CompactPlus1936.small1950,CompactPlus1936.nodes1950,NodePlus30.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus1936.p1951,GridPlus.atNode 1951,GridPlus.atNode 1952,NodePlus30.w31,CompactPlus1936.checked1951,CompactPlus1936.small1951,CompactPlus1936.nodes1951,NodePlus30.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus1952.p1952,GridPlus.atNode 1952,GridPlus.atNode 1953,NodePlus30.w32,CompactPlus1952.checked1952,CompactPlus1952.small1952,CompactPlus1952.nodes1952,NodePlus30.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus1952.p1953,GridPlus.atNode 1953,GridPlus.atNode 1954,NodePlus30.w33,CompactPlus1952.checked1953,CompactPlus1952.small1953,CompactPlus1952.nodes1953,NodePlus30.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus1952.p1954,GridPlus.atNode 1954,GridPlus.atNode 1955,NodePlus30.w34,CompactPlus1952.checked1954,CompactPlus1952.small1954,CompactPlus1952.nodes1954,NodePlus30.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus1952.p1955,GridPlus.atNode 1955,GridPlus.atNode 1956,NodePlus30.w35,CompactPlus1952.checked1955,CompactPlus1952.small1955,CompactPlus1952.nodes1955,NodePlus30.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus1952.p1956,GridPlus.atNode 1956,GridPlus.atNode 1957,NodePlus30.w36,CompactPlus1952.checked1956,CompactPlus1952.small1956,CompactPlus1952.nodes1956,NodePlus30.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus1952.p1957,GridPlus.atNode 1957,GridPlus.atNode 1958,NodePlus30.w37,CompactPlus1952.checked1957,CompactPlus1952.small1957,CompactPlus1952.nodes1957,NodePlus30.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus1952.p1958,GridPlus.atNode 1958,GridPlus.atNode 1959,NodePlus30.w38,CompactPlus1952.checked1958,CompactPlus1952.small1958,CompactPlus1952.nodes1958,NodePlus30.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus1952.p1959,GridPlus.atNode 1959,GridPlus.atNode 1960,NodePlus30.w39,CompactPlus1952.checked1959,CompactPlus1952.small1959,CompactPlus1952.nodes1959,NodePlus30.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus1952.p1960,GridPlus.atNode 1960,GridPlus.atNode 1961,NodePlus30.w40,CompactPlus1952.checked1960,CompactPlus1952.small1960,CompactPlus1952.nodes1960,NodePlus30.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus1952.p1961,GridPlus.atNode 1961,GridPlus.atNode 1962,NodePlus30.w41,CompactPlus1952.checked1961,CompactPlus1952.small1961,CompactPlus1952.nodes1961,NodePlus30.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus1952.p1962,GridPlus.atNode 1962,GridPlus.atNode 1963,NodePlus30.w42,CompactPlus1952.checked1962,CompactPlus1952.small1962,CompactPlus1952.nodes1962,NodePlus30.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus1952.p1963,GridPlus.atNode 1963,GridPlus.atNode 1964,NodePlus30.w43,CompactPlus1952.checked1963,CompactPlus1952.small1963,CompactPlus1952.nodes1963,NodePlus30.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus1952.p1964,GridPlus.atNode 1964,GridPlus.atNode 1965,NodePlus30.w44,CompactPlus1952.checked1964,CompactPlus1952.small1964,CompactPlus1952.nodes1964,NodePlus30.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus1952.p1965,GridPlus.atNode 1965,GridPlus.atNode 1966,NodePlus30.w45,CompactPlus1952.checked1965,CompactPlus1952.small1965,CompactPlus1952.nodes1965,NodePlus30.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus1952.p1966,GridPlus.atNode 1966,GridPlus.atNode 1967,NodePlus30.w46,CompactPlus1952.checked1966,CompactPlus1952.small1966,CompactPlus1952.nodes1966,NodePlus30.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus1952.p1967,GridPlus.atNode 1967,GridPlus.atNode 1968,NodePlus30.w47,CompactPlus1952.checked1967,CompactPlus1952.small1967,CompactPlus1952.nodes1967,NodePlus30.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus1968.p1968,GridPlus.atNode 1968,GridPlus.atNode 1969,NodePlus30.w48,CompactPlus1968.checked1968,CompactPlus1968.small1968,CompactPlus1968.nodes1968,NodePlus30.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus1968.p1969,GridPlus.atNode 1969,GridPlus.atNode 1970,NodePlus30.w49,CompactPlus1968.checked1969,CompactPlus1968.small1969,CompactPlus1968.nodes1969,NodePlus30.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus1968.p1970,GridPlus.atNode 1970,GridPlus.atNode 1971,NodePlus30.w50,CompactPlus1968.checked1970,CompactPlus1968.small1970,CompactPlus1968.nodes1970,NodePlus30.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus1968.p1971,GridPlus.atNode 1971,GridPlus.atNode 1972,NodePlus30.w51,CompactPlus1968.checked1971,CompactPlus1968.small1971,CompactPlus1968.nodes1971,NodePlus30.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus1968.p1972,GridPlus.atNode 1972,GridPlus.atNode 1973,NodePlus30.w52,CompactPlus1968.checked1972,CompactPlus1968.small1972,CompactPlus1968.nodes1972,NodePlus30.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus1968.p1973,GridPlus.atNode 1973,GridPlus.atNode 1974,NodePlus30.w53,CompactPlus1968.checked1973,CompactPlus1968.small1973,CompactPlus1968.nodes1973,NodePlus30.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus1968.p1974,GridPlus.atNode 1974,GridPlus.atNode 1975,NodePlus30.w54,CompactPlus1968.checked1974,CompactPlus1968.small1974,CompactPlus1968.nodes1974,NodePlus30.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus1968.p1975,GridPlus.atNode 1975,GridPlus.atNode 1976,NodePlus30.w55,CompactPlus1968.checked1975,CompactPlus1968.small1975,CompactPlus1968.nodes1975,NodePlus30.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus1968.p1976,GridPlus.atNode 1976,GridPlus.atNode 1977,NodePlus30.w56,CompactPlus1968.checked1976,CompactPlus1968.small1976,CompactPlus1968.nodes1976,NodePlus30.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus1968.p1977,GridPlus.atNode 1977,GridPlus.atNode 1978,NodePlus30.w57,CompactPlus1968.checked1977,CompactPlus1968.small1977,CompactPlus1968.nodes1977,NodePlus30.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus1968.p1978,GridPlus.atNode 1978,GridPlus.atNode 1979,NodePlus30.w58,CompactPlus1968.checked1978,CompactPlus1968.small1978,CompactPlus1968.nodes1978,NodePlus30.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus1968.p1979,GridPlus.atNode 1979,GridPlus.atNode 1980,NodePlus30.w59,CompactPlus1968.checked1979,CompactPlus1968.small1979,CompactPlus1968.nodes1979,NodePlus30.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus1968.p1980,GridPlus.atNode 1980,GridPlus.atNode 1981,NodePlus30.w60,CompactPlus1968.checked1980,CompactPlus1968.small1980,CompactPlus1968.nodes1980,NodePlus30.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus1968.p1981,GridPlus.atNode 1981,GridPlus.atNode 1982,NodePlus30.w61,CompactPlus1968.checked1981,CompactPlus1968.small1981,CompactPlus1968.nodes1981,NodePlus30.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus1968.p1982,GridPlus.atNode 1982,GridPlus.atNode 1983,NodePlus30.w62,CompactPlus1968.checked1982,CompactPlus1968.small1982,CompactPlus1968.nodes1982,NodePlus30.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus1968.p1983,GridPlus.atNode 1983,GridPlus.atNode 1984,NodePlus30.w63,CompactPlus1968.checked1983,CompactPlus1968.small1983,CompactPlus1968.nodes1983,NodePlus30.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (1920+j) ∧
    (atRow j).right=GridPlus.atNode (1920+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus30
