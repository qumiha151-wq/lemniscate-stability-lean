import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus1920
import SolitonClassification.Rotating.ResetPackedMinus1936
import SolitonClassification.Rotating.ResetPackedMinus1952
import SolitonClassification.Rotating.ResetPackedMinus1968
namespace SolitonClassification.Rotating.DyadicReset.TileMinus30
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1920.p1920,GridMinus.atNode 1920,GridMinus.atNode 1921,NodeMinus30.w0,CompactMinus1920.checked1920,CompactMinus1920.small1920,CompactMinus1920.nodes1920,NodeMinus30.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1920.p1921,GridMinus.atNode 1921,GridMinus.atNode 1922,NodeMinus30.w1,CompactMinus1920.checked1921,CompactMinus1920.small1921,CompactMinus1920.nodes1921,NodeMinus30.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1920.p1922,GridMinus.atNode 1922,GridMinus.atNode 1923,NodeMinus30.w2,CompactMinus1920.checked1922,CompactMinus1920.small1922,CompactMinus1920.nodes1922,NodeMinus30.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1920.p1923,GridMinus.atNode 1923,GridMinus.atNode 1924,NodeMinus30.w3,CompactMinus1920.checked1923,CompactMinus1920.small1923,CompactMinus1920.nodes1923,NodeMinus30.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1920.p1924,GridMinus.atNode 1924,GridMinus.atNode 1925,NodeMinus30.w4,CompactMinus1920.checked1924,CompactMinus1920.small1924,CompactMinus1920.nodes1924,NodeMinus30.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1920.p1925,GridMinus.atNode 1925,GridMinus.atNode 1926,NodeMinus30.w5,CompactMinus1920.checked1925,CompactMinus1920.small1925,CompactMinus1920.nodes1925,NodeMinus30.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1920.p1926,GridMinus.atNode 1926,GridMinus.atNode 1927,NodeMinus30.w6,CompactMinus1920.checked1926,CompactMinus1920.small1926,CompactMinus1920.nodes1926,NodeMinus30.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1920.p1927,GridMinus.atNode 1927,GridMinus.atNode 1928,NodeMinus30.w7,CompactMinus1920.checked1927,CompactMinus1920.small1927,CompactMinus1920.nodes1927,NodeMinus30.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1920.p1928,GridMinus.atNode 1928,GridMinus.atNode 1929,NodeMinus30.w8,CompactMinus1920.checked1928,CompactMinus1920.small1928,CompactMinus1920.nodes1928,NodeMinus30.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1920.p1929,GridMinus.atNode 1929,GridMinus.atNode 1930,NodeMinus30.w9,CompactMinus1920.checked1929,CompactMinus1920.small1929,CompactMinus1920.nodes1929,NodeMinus30.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1920.p1930,GridMinus.atNode 1930,GridMinus.atNode 1931,NodeMinus30.w10,CompactMinus1920.checked1930,CompactMinus1920.small1930,CompactMinus1920.nodes1930,NodeMinus30.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1920.p1931,GridMinus.atNode 1931,GridMinus.atNode 1932,NodeMinus30.w11,CompactMinus1920.checked1931,CompactMinus1920.small1931,CompactMinus1920.nodes1931,NodeMinus30.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1920.p1932,GridMinus.atNode 1932,GridMinus.atNode 1933,NodeMinus30.w12,CompactMinus1920.checked1932,CompactMinus1920.small1932,CompactMinus1920.nodes1932,NodeMinus30.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1920.p1933,GridMinus.atNode 1933,GridMinus.atNode 1934,NodeMinus30.w13,CompactMinus1920.checked1933,CompactMinus1920.small1933,CompactMinus1920.nodes1933,NodeMinus30.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1920.p1934,GridMinus.atNode 1934,GridMinus.atNode 1935,NodeMinus30.w14,CompactMinus1920.checked1934,CompactMinus1920.small1934,CompactMinus1920.nodes1934,NodeMinus30.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1920.p1935,GridMinus.atNode 1935,GridMinus.atNode 1936,NodeMinus30.w15,CompactMinus1920.checked1935,CompactMinus1920.small1935,CompactMinus1920.nodes1935,NodeMinus30.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1936.p1936,GridMinus.atNode 1936,GridMinus.atNode 1937,NodeMinus30.w16,CompactMinus1936.checked1936,CompactMinus1936.small1936,CompactMinus1936.nodes1936,NodeMinus30.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1936.p1937,GridMinus.atNode 1937,GridMinus.atNode 1938,NodeMinus30.w17,CompactMinus1936.checked1937,CompactMinus1936.small1937,CompactMinus1936.nodes1937,NodeMinus30.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1936.p1938,GridMinus.atNode 1938,GridMinus.atNode 1939,NodeMinus30.w18,CompactMinus1936.checked1938,CompactMinus1936.small1938,CompactMinus1936.nodes1938,NodeMinus30.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1936.p1939,GridMinus.atNode 1939,GridMinus.atNode 1940,NodeMinus30.w19,CompactMinus1936.checked1939,CompactMinus1936.small1939,CompactMinus1936.nodes1939,NodeMinus30.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1936.p1940,GridMinus.atNode 1940,GridMinus.atNode 1941,NodeMinus30.w20,CompactMinus1936.checked1940,CompactMinus1936.small1940,CompactMinus1936.nodes1940,NodeMinus30.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1936.p1941,GridMinus.atNode 1941,GridMinus.atNode 1942,NodeMinus30.w21,CompactMinus1936.checked1941,CompactMinus1936.small1941,CompactMinus1936.nodes1941,NodeMinus30.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1936.p1942,GridMinus.atNode 1942,GridMinus.atNode 1943,NodeMinus30.w22,CompactMinus1936.checked1942,CompactMinus1936.small1942,CompactMinus1936.nodes1942,NodeMinus30.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1936.p1943,GridMinus.atNode 1943,GridMinus.atNode 1944,NodeMinus30.w23,CompactMinus1936.checked1943,CompactMinus1936.small1943,CompactMinus1936.nodes1943,NodeMinus30.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1936.p1944,GridMinus.atNode 1944,GridMinus.atNode 1945,NodeMinus30.w24,CompactMinus1936.checked1944,CompactMinus1936.small1944,CompactMinus1936.nodes1944,NodeMinus30.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1936.p1945,GridMinus.atNode 1945,GridMinus.atNode 1946,NodeMinus30.w25,CompactMinus1936.checked1945,CompactMinus1936.small1945,CompactMinus1936.nodes1945,NodeMinus30.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1936.p1946,GridMinus.atNode 1946,GridMinus.atNode 1947,NodeMinus30.w26,CompactMinus1936.checked1946,CompactMinus1936.small1946,CompactMinus1936.nodes1946,NodeMinus30.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1936.p1947,GridMinus.atNode 1947,GridMinus.atNode 1948,NodeMinus30.w27,CompactMinus1936.checked1947,CompactMinus1936.small1947,CompactMinus1936.nodes1947,NodeMinus30.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1936.p1948,GridMinus.atNode 1948,GridMinus.atNode 1949,NodeMinus30.w28,CompactMinus1936.checked1948,CompactMinus1936.small1948,CompactMinus1936.nodes1948,NodeMinus30.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1936.p1949,GridMinus.atNode 1949,GridMinus.atNode 1950,NodeMinus30.w29,CompactMinus1936.checked1949,CompactMinus1936.small1949,CompactMinus1936.nodes1949,NodeMinus30.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1936.p1950,GridMinus.atNode 1950,GridMinus.atNode 1951,NodeMinus30.w30,CompactMinus1936.checked1950,CompactMinus1936.small1950,CompactMinus1936.nodes1950,NodeMinus30.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1936.p1951,GridMinus.atNode 1951,GridMinus.atNode 1952,NodeMinus30.w31,CompactMinus1936.checked1951,CompactMinus1936.small1951,CompactMinus1936.nodes1951,NodeMinus30.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1952.p1952,GridMinus.atNode 1952,GridMinus.atNode 1953,NodeMinus30.w32,CompactMinus1952.checked1952,CompactMinus1952.small1952,CompactMinus1952.nodes1952,NodeMinus30.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1952.p1953,GridMinus.atNode 1953,GridMinus.atNode 1954,NodeMinus30.w33,CompactMinus1952.checked1953,CompactMinus1952.small1953,CompactMinus1952.nodes1953,NodeMinus30.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1952.p1954,GridMinus.atNode 1954,GridMinus.atNode 1955,NodeMinus30.w34,CompactMinus1952.checked1954,CompactMinus1952.small1954,CompactMinus1952.nodes1954,NodeMinus30.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1952.p1955,GridMinus.atNode 1955,GridMinus.atNode 1956,NodeMinus30.w35,CompactMinus1952.checked1955,CompactMinus1952.small1955,CompactMinus1952.nodes1955,NodeMinus30.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1952.p1956,GridMinus.atNode 1956,GridMinus.atNode 1957,NodeMinus30.w36,CompactMinus1952.checked1956,CompactMinus1952.small1956,CompactMinus1952.nodes1956,NodeMinus30.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1952.p1957,GridMinus.atNode 1957,GridMinus.atNode 1958,NodeMinus30.w37,CompactMinus1952.checked1957,CompactMinus1952.small1957,CompactMinus1952.nodes1957,NodeMinus30.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1952.p1958,GridMinus.atNode 1958,GridMinus.atNode 1959,NodeMinus30.w38,CompactMinus1952.checked1958,CompactMinus1952.small1958,CompactMinus1952.nodes1958,NodeMinus30.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1952.p1959,GridMinus.atNode 1959,GridMinus.atNode 1960,NodeMinus30.w39,CompactMinus1952.checked1959,CompactMinus1952.small1959,CompactMinus1952.nodes1959,NodeMinus30.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1952.p1960,GridMinus.atNode 1960,GridMinus.atNode 1961,NodeMinus30.w40,CompactMinus1952.checked1960,CompactMinus1952.small1960,CompactMinus1952.nodes1960,NodeMinus30.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1952.p1961,GridMinus.atNode 1961,GridMinus.atNode 1962,NodeMinus30.w41,CompactMinus1952.checked1961,CompactMinus1952.small1961,CompactMinus1952.nodes1961,NodeMinus30.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1952.p1962,GridMinus.atNode 1962,GridMinus.atNode 1963,NodeMinus30.w42,CompactMinus1952.checked1962,CompactMinus1952.small1962,CompactMinus1952.nodes1962,NodeMinus30.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1952.p1963,GridMinus.atNode 1963,GridMinus.atNode 1964,NodeMinus30.w43,CompactMinus1952.checked1963,CompactMinus1952.small1963,CompactMinus1952.nodes1963,NodeMinus30.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1952.p1964,GridMinus.atNode 1964,GridMinus.atNode 1965,NodeMinus30.w44,CompactMinus1952.checked1964,CompactMinus1952.small1964,CompactMinus1952.nodes1964,NodeMinus30.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1952.p1965,GridMinus.atNode 1965,GridMinus.atNode 1966,NodeMinus30.w45,CompactMinus1952.checked1965,CompactMinus1952.small1965,CompactMinus1952.nodes1965,NodeMinus30.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1952.p1966,GridMinus.atNode 1966,GridMinus.atNode 1967,NodeMinus30.w46,CompactMinus1952.checked1966,CompactMinus1952.small1966,CompactMinus1952.nodes1966,NodeMinus30.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1952.p1967,GridMinus.atNode 1967,GridMinus.atNode 1968,NodeMinus30.w47,CompactMinus1952.checked1967,CompactMinus1952.small1967,CompactMinus1952.nodes1967,NodeMinus30.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1968.p1968,GridMinus.atNode 1968,GridMinus.atNode 1969,NodeMinus30.w48,CompactMinus1968.checked1968,CompactMinus1968.small1968,CompactMinus1968.nodes1968,NodeMinus30.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1968.p1969,GridMinus.atNode 1969,GridMinus.atNode 1970,NodeMinus30.w49,CompactMinus1968.checked1969,CompactMinus1968.small1969,CompactMinus1968.nodes1969,NodeMinus30.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1968.p1970,GridMinus.atNode 1970,GridMinus.atNode 1971,NodeMinus30.w50,CompactMinus1968.checked1970,CompactMinus1968.small1970,CompactMinus1968.nodes1970,NodeMinus30.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1968.p1971,GridMinus.atNode 1971,GridMinus.atNode 1972,NodeMinus30.w51,CompactMinus1968.checked1971,CompactMinus1968.small1971,CompactMinus1968.nodes1971,NodeMinus30.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1968.p1972,GridMinus.atNode 1972,GridMinus.atNode 1973,NodeMinus30.w52,CompactMinus1968.checked1972,CompactMinus1968.small1972,CompactMinus1968.nodes1972,NodeMinus30.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1968.p1973,GridMinus.atNode 1973,GridMinus.atNode 1974,NodeMinus30.w53,CompactMinus1968.checked1973,CompactMinus1968.small1973,CompactMinus1968.nodes1973,NodeMinus30.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1968.p1974,GridMinus.atNode 1974,GridMinus.atNode 1975,NodeMinus30.w54,CompactMinus1968.checked1974,CompactMinus1968.small1974,CompactMinus1968.nodes1974,NodeMinus30.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1968.p1975,GridMinus.atNode 1975,GridMinus.atNode 1976,NodeMinus30.w55,CompactMinus1968.checked1975,CompactMinus1968.small1975,CompactMinus1968.nodes1975,NodeMinus30.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1968.p1976,GridMinus.atNode 1976,GridMinus.atNode 1977,NodeMinus30.w56,CompactMinus1968.checked1976,CompactMinus1968.small1976,CompactMinus1968.nodes1976,NodeMinus30.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1968.p1977,GridMinus.atNode 1977,GridMinus.atNode 1978,NodeMinus30.w57,CompactMinus1968.checked1977,CompactMinus1968.small1977,CompactMinus1968.nodes1977,NodeMinus30.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1968.p1978,GridMinus.atNode 1978,GridMinus.atNode 1979,NodeMinus30.w58,CompactMinus1968.checked1978,CompactMinus1968.small1978,CompactMinus1968.nodes1978,NodeMinus30.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1968.p1979,GridMinus.atNode 1979,GridMinus.atNode 1980,NodeMinus30.w59,CompactMinus1968.checked1979,CompactMinus1968.small1979,CompactMinus1968.nodes1979,NodeMinus30.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1968.p1980,GridMinus.atNode 1980,GridMinus.atNode 1981,NodeMinus30.w60,CompactMinus1968.checked1980,CompactMinus1968.small1980,CompactMinus1968.nodes1980,NodeMinus30.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1968.p1981,GridMinus.atNode 1981,GridMinus.atNode 1982,NodeMinus30.w61,CompactMinus1968.checked1981,CompactMinus1968.small1981,CompactMinus1968.nodes1981,NodeMinus30.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1968.p1982,GridMinus.atNode 1982,GridMinus.atNode 1983,NodeMinus30.w62,CompactMinus1968.checked1982,CompactMinus1968.small1982,CompactMinus1968.nodes1982,NodeMinus30.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus1968.p1983,GridMinus.atNode 1983,GridMinus.atNode 1984,NodeMinus30.w63,CompactMinus1968.checked1983,CompactMinus1968.small1983,CompactMinus1968.nodes1983,NodeMinus30.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (1920+j) ∧
    (atRow j).right=GridMinus.atNode (1920+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus30
