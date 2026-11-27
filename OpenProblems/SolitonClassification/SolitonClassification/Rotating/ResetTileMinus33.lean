import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus2112
import SolitonClassification.Rotating.ResetPackedMinus2128
import SolitonClassification.Rotating.ResetPackedMinus2144
import SolitonClassification.Rotating.ResetPackedMinus2160
namespace SolitonClassification.Rotating.DyadicReset.TileMinus33
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2112.p2112,GridMinus.atNode 2112,GridMinus.atNode 2113,NodeMinus33.w0,CompactMinus2112.checked2112,CompactMinus2112.small2112,CompactMinus2112.nodes2112,NodeMinus33.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2112.p2113,GridMinus.atNode 2113,GridMinus.atNode 2114,NodeMinus33.w1,CompactMinus2112.checked2113,CompactMinus2112.small2113,CompactMinus2112.nodes2113,NodeMinus33.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2112.p2114,GridMinus.atNode 2114,GridMinus.atNode 2115,NodeMinus33.w2,CompactMinus2112.checked2114,CompactMinus2112.small2114,CompactMinus2112.nodes2114,NodeMinus33.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2112.p2115,GridMinus.atNode 2115,GridMinus.atNode 2116,NodeMinus33.w3,CompactMinus2112.checked2115,CompactMinus2112.small2115,CompactMinus2112.nodes2115,NodeMinus33.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2112.p2116,GridMinus.atNode 2116,GridMinus.atNode 2117,NodeMinus33.w4,CompactMinus2112.checked2116,CompactMinus2112.small2116,CompactMinus2112.nodes2116,NodeMinus33.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2112.p2117,GridMinus.atNode 2117,GridMinus.atNode 2118,NodeMinus33.w5,CompactMinus2112.checked2117,CompactMinus2112.small2117,CompactMinus2112.nodes2117,NodeMinus33.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2112.p2118,GridMinus.atNode 2118,GridMinus.atNode 2119,NodeMinus33.w6,CompactMinus2112.checked2118,CompactMinus2112.small2118,CompactMinus2112.nodes2118,NodeMinus33.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2112.p2119,GridMinus.atNode 2119,GridMinus.atNode 2120,NodeMinus33.w7,CompactMinus2112.checked2119,CompactMinus2112.small2119,CompactMinus2112.nodes2119,NodeMinus33.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2112.p2120,GridMinus.atNode 2120,GridMinus.atNode 2121,NodeMinus33.w8,CompactMinus2112.checked2120,CompactMinus2112.small2120,CompactMinus2112.nodes2120,NodeMinus33.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2112.p2121,GridMinus.atNode 2121,GridMinus.atNode 2122,NodeMinus33.w9,CompactMinus2112.checked2121,CompactMinus2112.small2121,CompactMinus2112.nodes2121,NodeMinus33.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2112.p2122,GridMinus.atNode 2122,GridMinus.atNode 2123,NodeMinus33.w10,CompactMinus2112.checked2122,CompactMinus2112.small2122,CompactMinus2112.nodes2122,NodeMinus33.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2112.p2123,GridMinus.atNode 2123,GridMinus.atNode 2124,NodeMinus33.w11,CompactMinus2112.checked2123,CompactMinus2112.small2123,CompactMinus2112.nodes2123,NodeMinus33.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2112.p2124,GridMinus.atNode 2124,GridMinus.atNode 2125,NodeMinus33.w12,CompactMinus2112.checked2124,CompactMinus2112.small2124,CompactMinus2112.nodes2124,NodeMinus33.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2112.p2125,GridMinus.atNode 2125,GridMinus.atNode 2126,NodeMinus33.w13,CompactMinus2112.checked2125,CompactMinus2112.small2125,CompactMinus2112.nodes2125,NodeMinus33.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2112.p2126,GridMinus.atNode 2126,GridMinus.atNode 2127,NodeMinus33.w14,CompactMinus2112.checked2126,CompactMinus2112.small2126,CompactMinus2112.nodes2126,NodeMinus33.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2112.p2127,GridMinus.atNode 2127,GridMinus.atNode 2128,NodeMinus33.w15,CompactMinus2112.checked2127,CompactMinus2112.small2127,CompactMinus2112.nodes2127,NodeMinus33.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2128.p2128,GridMinus.atNode 2128,GridMinus.atNode 2129,NodeMinus33.w16,CompactMinus2128.checked2128,CompactMinus2128.small2128,CompactMinus2128.nodes2128,NodeMinus33.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2128.p2129,GridMinus.atNode 2129,GridMinus.atNode 2130,NodeMinus33.w17,CompactMinus2128.checked2129,CompactMinus2128.small2129,CompactMinus2128.nodes2129,NodeMinus33.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2128.p2130,GridMinus.atNode 2130,GridMinus.atNode 2131,NodeMinus33.w18,CompactMinus2128.checked2130,CompactMinus2128.small2130,CompactMinus2128.nodes2130,NodeMinus33.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2128.p2131,GridMinus.atNode 2131,GridMinus.atNode 2132,NodeMinus33.w19,CompactMinus2128.checked2131,CompactMinus2128.small2131,CompactMinus2128.nodes2131,NodeMinus33.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2128.p2132,GridMinus.atNode 2132,GridMinus.atNode 2133,NodeMinus33.w20,CompactMinus2128.checked2132,CompactMinus2128.small2132,CompactMinus2128.nodes2132,NodeMinus33.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2128.p2133,GridMinus.atNode 2133,GridMinus.atNode 2134,NodeMinus33.w21,CompactMinus2128.checked2133,CompactMinus2128.small2133,CompactMinus2128.nodes2133,NodeMinus33.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2128.p2134,GridMinus.atNode 2134,GridMinus.atNode 2135,NodeMinus33.w22,CompactMinus2128.checked2134,CompactMinus2128.small2134,CompactMinus2128.nodes2134,NodeMinus33.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2128.p2135,GridMinus.atNode 2135,GridMinus.atNode 2136,NodeMinus33.w23,CompactMinus2128.checked2135,CompactMinus2128.small2135,CompactMinus2128.nodes2135,NodeMinus33.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2128.p2136,GridMinus.atNode 2136,GridMinus.atNode 2137,NodeMinus33.w24,CompactMinus2128.checked2136,CompactMinus2128.small2136,CompactMinus2128.nodes2136,NodeMinus33.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2128.p2137,GridMinus.atNode 2137,GridMinus.atNode 2138,NodeMinus33.w25,CompactMinus2128.checked2137,CompactMinus2128.small2137,CompactMinus2128.nodes2137,NodeMinus33.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2128.p2138,GridMinus.atNode 2138,GridMinus.atNode 2139,NodeMinus33.w26,CompactMinus2128.checked2138,CompactMinus2128.small2138,CompactMinus2128.nodes2138,NodeMinus33.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2128.p2139,GridMinus.atNode 2139,GridMinus.atNode 2140,NodeMinus33.w27,CompactMinus2128.checked2139,CompactMinus2128.small2139,CompactMinus2128.nodes2139,NodeMinus33.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2128.p2140,GridMinus.atNode 2140,GridMinus.atNode 2141,NodeMinus33.w28,CompactMinus2128.checked2140,CompactMinus2128.small2140,CompactMinus2128.nodes2140,NodeMinus33.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2128.p2141,GridMinus.atNode 2141,GridMinus.atNode 2142,NodeMinus33.w29,CompactMinus2128.checked2141,CompactMinus2128.small2141,CompactMinus2128.nodes2141,NodeMinus33.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2128.p2142,GridMinus.atNode 2142,GridMinus.atNode 2143,NodeMinus33.w30,CompactMinus2128.checked2142,CompactMinus2128.small2142,CompactMinus2128.nodes2142,NodeMinus33.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2128.p2143,GridMinus.atNode 2143,GridMinus.atNode 2144,NodeMinus33.w31,CompactMinus2128.checked2143,CompactMinus2128.small2143,CompactMinus2128.nodes2143,NodeMinus33.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2144.p2144,GridMinus.atNode 2144,GridMinus.atNode 2145,NodeMinus33.w32,CompactMinus2144.checked2144,CompactMinus2144.small2144,CompactMinus2144.nodes2144,NodeMinus33.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2144.p2145,GridMinus.atNode 2145,GridMinus.atNode 2146,NodeMinus33.w33,CompactMinus2144.checked2145,CompactMinus2144.small2145,CompactMinus2144.nodes2145,NodeMinus33.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2144.p2146,GridMinus.atNode 2146,GridMinus.atNode 2147,NodeMinus33.w34,CompactMinus2144.checked2146,CompactMinus2144.small2146,CompactMinus2144.nodes2146,NodeMinus33.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2144.p2147,GridMinus.atNode 2147,GridMinus.atNode 2148,NodeMinus33.w35,CompactMinus2144.checked2147,CompactMinus2144.small2147,CompactMinus2144.nodes2147,NodeMinus33.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2144.p2148,GridMinus.atNode 2148,GridMinus.atNode 2149,NodeMinus33.w36,CompactMinus2144.checked2148,CompactMinus2144.small2148,CompactMinus2144.nodes2148,NodeMinus33.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2144.p2149,GridMinus.atNode 2149,GridMinus.atNode 2150,NodeMinus33.w37,CompactMinus2144.checked2149,CompactMinus2144.small2149,CompactMinus2144.nodes2149,NodeMinus33.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2144.p2150,GridMinus.atNode 2150,GridMinus.atNode 2151,NodeMinus33.w38,CompactMinus2144.checked2150,CompactMinus2144.small2150,CompactMinus2144.nodes2150,NodeMinus33.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2144.p2151,GridMinus.atNode 2151,GridMinus.atNode 2152,NodeMinus33.w39,CompactMinus2144.checked2151,CompactMinus2144.small2151,CompactMinus2144.nodes2151,NodeMinus33.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2144.p2152,GridMinus.atNode 2152,GridMinus.atNode 2153,NodeMinus33.w40,CompactMinus2144.checked2152,CompactMinus2144.small2152,CompactMinus2144.nodes2152,NodeMinus33.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2144.p2153,GridMinus.atNode 2153,GridMinus.atNode 2154,NodeMinus33.w41,CompactMinus2144.checked2153,CompactMinus2144.small2153,CompactMinus2144.nodes2153,NodeMinus33.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2144.p2154,GridMinus.atNode 2154,GridMinus.atNode 2155,NodeMinus33.w42,CompactMinus2144.checked2154,CompactMinus2144.small2154,CompactMinus2144.nodes2154,NodeMinus33.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2144.p2155,GridMinus.atNode 2155,GridMinus.atNode 2156,NodeMinus33.w43,CompactMinus2144.checked2155,CompactMinus2144.small2155,CompactMinus2144.nodes2155,NodeMinus33.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2144.p2156,GridMinus.atNode 2156,GridMinus.atNode 2157,NodeMinus33.w44,CompactMinus2144.checked2156,CompactMinus2144.small2156,CompactMinus2144.nodes2156,NodeMinus33.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2144.p2157,GridMinus.atNode 2157,GridMinus.atNode 2158,NodeMinus33.w45,CompactMinus2144.checked2157,CompactMinus2144.small2157,CompactMinus2144.nodes2157,NodeMinus33.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2144.p2158,GridMinus.atNode 2158,GridMinus.atNode 2159,NodeMinus33.w46,CompactMinus2144.checked2158,CompactMinus2144.small2158,CompactMinus2144.nodes2158,NodeMinus33.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2144.p2159,GridMinus.atNode 2159,GridMinus.atNode 2160,NodeMinus33.w47,CompactMinus2144.checked2159,CompactMinus2144.small2159,CompactMinus2144.nodes2159,NodeMinus33.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2160.p2160,GridMinus.atNode 2160,GridMinus.atNode 2161,NodeMinus33.w48,CompactMinus2160.checked2160,CompactMinus2160.small2160,CompactMinus2160.nodes2160,NodeMinus33.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2160.p2161,GridMinus.atNode 2161,GridMinus.atNode 2162,NodeMinus33.w49,CompactMinus2160.checked2161,CompactMinus2160.small2161,CompactMinus2160.nodes2161,NodeMinus33.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2160.p2162,GridMinus.atNode 2162,GridMinus.atNode 2163,NodeMinus33.w50,CompactMinus2160.checked2162,CompactMinus2160.small2162,CompactMinus2160.nodes2162,NodeMinus33.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2160.p2163,GridMinus.atNode 2163,GridMinus.atNode 2164,NodeMinus33.w51,CompactMinus2160.checked2163,CompactMinus2160.small2163,CompactMinus2160.nodes2163,NodeMinus33.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2160.p2164,GridMinus.atNode 2164,GridMinus.atNode 2165,NodeMinus33.w52,CompactMinus2160.checked2164,CompactMinus2160.small2164,CompactMinus2160.nodes2164,NodeMinus33.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2160.p2165,GridMinus.atNode 2165,GridMinus.atNode 2166,NodeMinus33.w53,CompactMinus2160.checked2165,CompactMinus2160.small2165,CompactMinus2160.nodes2165,NodeMinus33.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2160.p2166,GridMinus.atNode 2166,GridMinus.atNode 2167,NodeMinus33.w54,CompactMinus2160.checked2166,CompactMinus2160.small2166,CompactMinus2160.nodes2166,NodeMinus33.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2160.p2167,GridMinus.atNode 2167,GridMinus.atNode 2168,NodeMinus33.w55,CompactMinus2160.checked2167,CompactMinus2160.small2167,CompactMinus2160.nodes2167,NodeMinus33.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2160.p2168,GridMinus.atNode 2168,GridMinus.atNode 2169,NodeMinus33.w56,CompactMinus2160.checked2168,CompactMinus2160.small2168,CompactMinus2160.nodes2168,NodeMinus33.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2160.p2169,GridMinus.atNode 2169,GridMinus.atNode 2170,NodeMinus33.w57,CompactMinus2160.checked2169,CompactMinus2160.small2169,CompactMinus2160.nodes2169,NodeMinus33.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2160.p2170,GridMinus.atNode 2170,GridMinus.atNode 2171,NodeMinus33.w58,CompactMinus2160.checked2170,CompactMinus2160.small2170,CompactMinus2160.nodes2170,NodeMinus33.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2160.p2171,GridMinus.atNode 2171,GridMinus.atNode 2172,NodeMinus33.w59,CompactMinus2160.checked2171,CompactMinus2160.small2171,CompactMinus2160.nodes2171,NodeMinus33.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2160.p2172,GridMinus.atNode 2172,GridMinus.atNode 2173,NodeMinus33.w60,CompactMinus2160.checked2172,CompactMinus2160.small2172,CompactMinus2160.nodes2172,NodeMinus33.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2160.p2173,GridMinus.atNode 2173,GridMinus.atNode 2174,NodeMinus33.w61,CompactMinus2160.checked2173,CompactMinus2160.small2173,CompactMinus2160.nodes2173,NodeMinus33.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2160.p2174,GridMinus.atNode 2174,GridMinus.atNode 2175,NodeMinus33.w62,CompactMinus2160.checked2174,CompactMinus2160.small2174,CompactMinus2160.nodes2174,NodeMinus33.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2160.p2175,GridMinus.atNode 2175,GridMinus.atNode 2176,NodeMinus33.w63,CompactMinus2160.checked2175,CompactMinus2160.small2175,CompactMinus2160.nodes2175,NodeMinus33.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (2112+j) ∧
    (atRow j).right=GridMinus.atNode (2112+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus33
