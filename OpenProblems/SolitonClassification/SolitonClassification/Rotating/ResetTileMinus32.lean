import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus2048
import SolitonClassification.Rotating.ResetPackedMinus2064
import SolitonClassification.Rotating.ResetPackedMinus2080
import SolitonClassification.Rotating.ResetPackedMinus2096
namespace SolitonClassification.Rotating.DyadicReset.TileMinus32
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2048.p2048,GridMinus.atNode 2048,GridMinus.atNode 2049,NodeMinus32.w0,CompactMinus2048.checked2048,CompactMinus2048.small2048,CompactMinus2048.nodes2048,NodeMinus32.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2048.p2049,GridMinus.atNode 2049,GridMinus.atNode 2050,NodeMinus32.w1,CompactMinus2048.checked2049,CompactMinus2048.small2049,CompactMinus2048.nodes2049,NodeMinus32.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2048.p2050,GridMinus.atNode 2050,GridMinus.atNode 2051,NodeMinus32.w2,CompactMinus2048.checked2050,CompactMinus2048.small2050,CompactMinus2048.nodes2050,NodeMinus32.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2048.p2051,GridMinus.atNode 2051,GridMinus.atNode 2052,NodeMinus32.w3,CompactMinus2048.checked2051,CompactMinus2048.small2051,CompactMinus2048.nodes2051,NodeMinus32.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2048.p2052,GridMinus.atNode 2052,GridMinus.atNode 2053,NodeMinus32.w4,CompactMinus2048.checked2052,CompactMinus2048.small2052,CompactMinus2048.nodes2052,NodeMinus32.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2048.p2053,GridMinus.atNode 2053,GridMinus.atNode 2054,NodeMinus32.w5,CompactMinus2048.checked2053,CompactMinus2048.small2053,CompactMinus2048.nodes2053,NodeMinus32.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2048.p2054,GridMinus.atNode 2054,GridMinus.atNode 2055,NodeMinus32.w6,CompactMinus2048.checked2054,CompactMinus2048.small2054,CompactMinus2048.nodes2054,NodeMinus32.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2048.p2055,GridMinus.atNode 2055,GridMinus.atNode 2056,NodeMinus32.w7,CompactMinus2048.checked2055,CompactMinus2048.small2055,CompactMinus2048.nodes2055,NodeMinus32.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2048.p2056,GridMinus.atNode 2056,GridMinus.atNode 2057,NodeMinus32.w8,CompactMinus2048.checked2056,CompactMinus2048.small2056,CompactMinus2048.nodes2056,NodeMinus32.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2048.p2057,GridMinus.atNode 2057,GridMinus.atNode 2058,NodeMinus32.w9,CompactMinus2048.checked2057,CompactMinus2048.small2057,CompactMinus2048.nodes2057,NodeMinus32.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2048.p2058,GridMinus.atNode 2058,GridMinus.atNode 2059,NodeMinus32.w10,CompactMinus2048.checked2058,CompactMinus2048.small2058,CompactMinus2048.nodes2058,NodeMinus32.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2048.p2059,GridMinus.atNode 2059,GridMinus.atNode 2060,NodeMinus32.w11,CompactMinus2048.checked2059,CompactMinus2048.small2059,CompactMinus2048.nodes2059,NodeMinus32.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2048.p2060,GridMinus.atNode 2060,GridMinus.atNode 2061,NodeMinus32.w12,CompactMinus2048.checked2060,CompactMinus2048.small2060,CompactMinus2048.nodes2060,NodeMinus32.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2048.p2061,GridMinus.atNode 2061,GridMinus.atNode 2062,NodeMinus32.w13,CompactMinus2048.checked2061,CompactMinus2048.small2061,CompactMinus2048.nodes2061,NodeMinus32.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2048.p2062,GridMinus.atNode 2062,GridMinus.atNode 2063,NodeMinus32.w14,CompactMinus2048.checked2062,CompactMinus2048.small2062,CompactMinus2048.nodes2062,NodeMinus32.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2048.p2063,GridMinus.atNode 2063,GridMinus.atNode 2064,NodeMinus32.w15,CompactMinus2048.checked2063,CompactMinus2048.small2063,CompactMinus2048.nodes2063,NodeMinus32.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2064.p2064,GridMinus.atNode 2064,GridMinus.atNode 2065,NodeMinus32.w16,CompactMinus2064.checked2064,CompactMinus2064.small2064,CompactMinus2064.nodes2064,NodeMinus32.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2064.p2065,GridMinus.atNode 2065,GridMinus.atNode 2066,NodeMinus32.w17,CompactMinus2064.checked2065,CompactMinus2064.small2065,CompactMinus2064.nodes2065,NodeMinus32.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2064.p2066,GridMinus.atNode 2066,GridMinus.atNode 2067,NodeMinus32.w18,CompactMinus2064.checked2066,CompactMinus2064.small2066,CompactMinus2064.nodes2066,NodeMinus32.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2064.p2067,GridMinus.atNode 2067,GridMinus.atNode 2068,NodeMinus32.w19,CompactMinus2064.checked2067,CompactMinus2064.small2067,CompactMinus2064.nodes2067,NodeMinus32.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2064.p2068,GridMinus.atNode 2068,GridMinus.atNode 2069,NodeMinus32.w20,CompactMinus2064.checked2068,CompactMinus2064.small2068,CompactMinus2064.nodes2068,NodeMinus32.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2064.p2069,GridMinus.atNode 2069,GridMinus.atNode 2070,NodeMinus32.w21,CompactMinus2064.checked2069,CompactMinus2064.small2069,CompactMinus2064.nodes2069,NodeMinus32.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2064.p2070,GridMinus.atNode 2070,GridMinus.atNode 2071,NodeMinus32.w22,CompactMinus2064.checked2070,CompactMinus2064.small2070,CompactMinus2064.nodes2070,NodeMinus32.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2064.p2071,GridMinus.atNode 2071,GridMinus.atNode 2072,NodeMinus32.w23,CompactMinus2064.checked2071,CompactMinus2064.small2071,CompactMinus2064.nodes2071,NodeMinus32.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2064.p2072,GridMinus.atNode 2072,GridMinus.atNode 2073,NodeMinus32.w24,CompactMinus2064.checked2072,CompactMinus2064.small2072,CompactMinus2064.nodes2072,NodeMinus32.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2064.p2073,GridMinus.atNode 2073,GridMinus.atNode 2074,NodeMinus32.w25,CompactMinus2064.checked2073,CompactMinus2064.small2073,CompactMinus2064.nodes2073,NodeMinus32.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2064.p2074,GridMinus.atNode 2074,GridMinus.atNode 2075,NodeMinus32.w26,CompactMinus2064.checked2074,CompactMinus2064.small2074,CompactMinus2064.nodes2074,NodeMinus32.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2064.p2075,GridMinus.atNode 2075,GridMinus.atNode 2076,NodeMinus32.w27,CompactMinus2064.checked2075,CompactMinus2064.small2075,CompactMinus2064.nodes2075,NodeMinus32.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2064.p2076,GridMinus.atNode 2076,GridMinus.atNode 2077,NodeMinus32.w28,CompactMinus2064.checked2076,CompactMinus2064.small2076,CompactMinus2064.nodes2076,NodeMinus32.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2064.p2077,GridMinus.atNode 2077,GridMinus.atNode 2078,NodeMinus32.w29,CompactMinus2064.checked2077,CompactMinus2064.small2077,CompactMinus2064.nodes2077,NodeMinus32.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2064.p2078,GridMinus.atNode 2078,GridMinus.atNode 2079,NodeMinus32.w30,CompactMinus2064.checked2078,CompactMinus2064.small2078,CompactMinus2064.nodes2078,NodeMinus32.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2064.p2079,GridMinus.atNode 2079,GridMinus.atNode 2080,NodeMinus32.w31,CompactMinus2064.checked2079,CompactMinus2064.small2079,CompactMinus2064.nodes2079,NodeMinus32.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2080.p2080,GridMinus.atNode 2080,GridMinus.atNode 2081,NodeMinus32.w32,CompactMinus2080.checked2080,CompactMinus2080.small2080,CompactMinus2080.nodes2080,NodeMinus32.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2080.p2081,GridMinus.atNode 2081,GridMinus.atNode 2082,NodeMinus32.w33,CompactMinus2080.checked2081,CompactMinus2080.small2081,CompactMinus2080.nodes2081,NodeMinus32.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2080.p2082,GridMinus.atNode 2082,GridMinus.atNode 2083,NodeMinus32.w34,CompactMinus2080.checked2082,CompactMinus2080.small2082,CompactMinus2080.nodes2082,NodeMinus32.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2080.p2083,GridMinus.atNode 2083,GridMinus.atNode 2084,NodeMinus32.w35,CompactMinus2080.checked2083,CompactMinus2080.small2083,CompactMinus2080.nodes2083,NodeMinus32.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2080.p2084,GridMinus.atNode 2084,GridMinus.atNode 2085,NodeMinus32.w36,CompactMinus2080.checked2084,CompactMinus2080.small2084,CompactMinus2080.nodes2084,NodeMinus32.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2080.p2085,GridMinus.atNode 2085,GridMinus.atNode 2086,NodeMinus32.w37,CompactMinus2080.checked2085,CompactMinus2080.small2085,CompactMinus2080.nodes2085,NodeMinus32.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2080.p2086,GridMinus.atNode 2086,GridMinus.atNode 2087,NodeMinus32.w38,CompactMinus2080.checked2086,CompactMinus2080.small2086,CompactMinus2080.nodes2086,NodeMinus32.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2080.p2087,GridMinus.atNode 2087,GridMinus.atNode 2088,NodeMinus32.w39,CompactMinus2080.checked2087,CompactMinus2080.small2087,CompactMinus2080.nodes2087,NodeMinus32.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2080.p2088,GridMinus.atNode 2088,GridMinus.atNode 2089,NodeMinus32.w40,CompactMinus2080.checked2088,CompactMinus2080.small2088,CompactMinus2080.nodes2088,NodeMinus32.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2080.p2089,GridMinus.atNode 2089,GridMinus.atNode 2090,NodeMinus32.w41,CompactMinus2080.checked2089,CompactMinus2080.small2089,CompactMinus2080.nodes2089,NodeMinus32.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2080.p2090,GridMinus.atNode 2090,GridMinus.atNode 2091,NodeMinus32.w42,CompactMinus2080.checked2090,CompactMinus2080.small2090,CompactMinus2080.nodes2090,NodeMinus32.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2080.p2091,GridMinus.atNode 2091,GridMinus.atNode 2092,NodeMinus32.w43,CompactMinus2080.checked2091,CompactMinus2080.small2091,CompactMinus2080.nodes2091,NodeMinus32.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2080.p2092,GridMinus.atNode 2092,GridMinus.atNode 2093,NodeMinus32.w44,CompactMinus2080.checked2092,CompactMinus2080.small2092,CompactMinus2080.nodes2092,NodeMinus32.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2080.p2093,GridMinus.atNode 2093,GridMinus.atNode 2094,NodeMinus32.w45,CompactMinus2080.checked2093,CompactMinus2080.small2093,CompactMinus2080.nodes2093,NodeMinus32.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2080.p2094,GridMinus.atNode 2094,GridMinus.atNode 2095,NodeMinus32.w46,CompactMinus2080.checked2094,CompactMinus2080.small2094,CompactMinus2080.nodes2094,NodeMinus32.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2080.p2095,GridMinus.atNode 2095,GridMinus.atNode 2096,NodeMinus32.w47,CompactMinus2080.checked2095,CompactMinus2080.small2095,CompactMinus2080.nodes2095,NodeMinus32.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2096.p2096,GridMinus.atNode 2096,GridMinus.atNode 2097,NodeMinus32.w48,CompactMinus2096.checked2096,CompactMinus2096.small2096,CompactMinus2096.nodes2096,NodeMinus32.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2096.p2097,GridMinus.atNode 2097,GridMinus.atNode 2098,NodeMinus32.w49,CompactMinus2096.checked2097,CompactMinus2096.small2097,CompactMinus2096.nodes2097,NodeMinus32.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2096.p2098,GridMinus.atNode 2098,GridMinus.atNode 2099,NodeMinus32.w50,CompactMinus2096.checked2098,CompactMinus2096.small2098,CompactMinus2096.nodes2098,NodeMinus32.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2096.p2099,GridMinus.atNode 2099,GridMinus.atNode 2100,NodeMinus32.w51,CompactMinus2096.checked2099,CompactMinus2096.small2099,CompactMinus2096.nodes2099,NodeMinus32.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2096.p2100,GridMinus.atNode 2100,GridMinus.atNode 2101,NodeMinus32.w52,CompactMinus2096.checked2100,CompactMinus2096.small2100,CompactMinus2096.nodes2100,NodeMinus32.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2096.p2101,GridMinus.atNode 2101,GridMinus.atNode 2102,NodeMinus32.w53,CompactMinus2096.checked2101,CompactMinus2096.small2101,CompactMinus2096.nodes2101,NodeMinus32.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2096.p2102,GridMinus.atNode 2102,GridMinus.atNode 2103,NodeMinus32.w54,CompactMinus2096.checked2102,CompactMinus2096.small2102,CompactMinus2096.nodes2102,NodeMinus32.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2096.p2103,GridMinus.atNode 2103,GridMinus.atNode 2104,NodeMinus32.w55,CompactMinus2096.checked2103,CompactMinus2096.small2103,CompactMinus2096.nodes2103,NodeMinus32.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2096.p2104,GridMinus.atNode 2104,GridMinus.atNode 2105,NodeMinus32.w56,CompactMinus2096.checked2104,CompactMinus2096.small2104,CompactMinus2096.nodes2104,NodeMinus32.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2096.p2105,GridMinus.atNode 2105,GridMinus.atNode 2106,NodeMinus32.w57,CompactMinus2096.checked2105,CompactMinus2096.small2105,CompactMinus2096.nodes2105,NodeMinus32.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2096.p2106,GridMinus.atNode 2106,GridMinus.atNode 2107,NodeMinus32.w58,CompactMinus2096.checked2106,CompactMinus2096.small2106,CompactMinus2096.nodes2106,NodeMinus32.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2096.p2107,GridMinus.atNode 2107,GridMinus.atNode 2108,NodeMinus32.w59,CompactMinus2096.checked2107,CompactMinus2096.small2107,CompactMinus2096.nodes2107,NodeMinus32.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2096.p2108,GridMinus.atNode 2108,GridMinus.atNode 2109,NodeMinus32.w60,CompactMinus2096.checked2108,CompactMinus2096.small2108,CompactMinus2096.nodes2108,NodeMinus32.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2096.p2109,GridMinus.atNode 2109,GridMinus.atNode 2110,NodeMinus32.w61,CompactMinus2096.checked2109,CompactMinus2096.small2109,CompactMinus2096.nodes2109,NodeMinus32.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2096.p2110,GridMinus.atNode 2110,GridMinus.atNode 2111,NodeMinus32.w62,CompactMinus2096.checked2110,CompactMinus2096.small2110,CompactMinus2096.nodes2110,NodeMinus32.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2096.p2111,GridMinus.atNode 2111,GridMinus.atNode 2112,NodeMinus32.w63,CompactMinus2096.checked2111,CompactMinus2096.small2111,CompactMinus2096.nodes2111,NodeMinus32.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (2048+j) ∧
    (atRow j).right=GridMinus.atNode (2048+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus32
