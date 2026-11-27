import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus2176
import SolitonClassification.Rotating.ResetPackedMinus2192
import SolitonClassification.Rotating.ResetPackedMinus2208
import SolitonClassification.Rotating.ResetPackedMinus2224
namespace SolitonClassification.Rotating.DyadicReset.TileMinus34
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2176.p2176,GridMinus.atNode 2176,GridMinus.atNode 2177,NodeMinus34.w0,CompactMinus2176.checked2176,CompactMinus2176.small2176,CompactMinus2176.nodes2176,NodeMinus34.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2176.p2177,GridMinus.atNode 2177,GridMinus.atNode 2178,NodeMinus34.w1,CompactMinus2176.checked2177,CompactMinus2176.small2177,CompactMinus2176.nodes2177,NodeMinus34.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2176.p2178,GridMinus.atNode 2178,GridMinus.atNode 2179,NodeMinus34.w2,CompactMinus2176.checked2178,CompactMinus2176.small2178,CompactMinus2176.nodes2178,NodeMinus34.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2176.p2179,GridMinus.atNode 2179,GridMinus.atNode 2180,NodeMinus34.w3,CompactMinus2176.checked2179,CompactMinus2176.small2179,CompactMinus2176.nodes2179,NodeMinus34.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2176.p2180,GridMinus.atNode 2180,GridMinus.atNode 2181,NodeMinus34.w4,CompactMinus2176.checked2180,CompactMinus2176.small2180,CompactMinus2176.nodes2180,NodeMinus34.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2176.p2181,GridMinus.atNode 2181,GridMinus.atNode 2182,NodeMinus34.w5,CompactMinus2176.checked2181,CompactMinus2176.small2181,CompactMinus2176.nodes2181,NodeMinus34.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2176.p2182,GridMinus.atNode 2182,GridMinus.atNode 2183,NodeMinus34.w6,CompactMinus2176.checked2182,CompactMinus2176.small2182,CompactMinus2176.nodes2182,NodeMinus34.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2176.p2183,GridMinus.atNode 2183,GridMinus.atNode 2184,NodeMinus34.w7,CompactMinus2176.checked2183,CompactMinus2176.small2183,CompactMinus2176.nodes2183,NodeMinus34.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2176.p2184,GridMinus.atNode 2184,GridMinus.atNode 2185,NodeMinus34.w8,CompactMinus2176.checked2184,CompactMinus2176.small2184,CompactMinus2176.nodes2184,NodeMinus34.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2176.p2185,GridMinus.atNode 2185,GridMinus.atNode 2186,NodeMinus34.w9,CompactMinus2176.checked2185,CompactMinus2176.small2185,CompactMinus2176.nodes2185,NodeMinus34.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2176.p2186,GridMinus.atNode 2186,GridMinus.atNode 2187,NodeMinus34.w10,CompactMinus2176.checked2186,CompactMinus2176.small2186,CompactMinus2176.nodes2186,NodeMinus34.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2176.p2187,GridMinus.atNode 2187,GridMinus.atNode 2188,NodeMinus34.w11,CompactMinus2176.checked2187,CompactMinus2176.small2187,CompactMinus2176.nodes2187,NodeMinus34.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2176.p2188,GridMinus.atNode 2188,GridMinus.atNode 2189,NodeMinus34.w12,CompactMinus2176.checked2188,CompactMinus2176.small2188,CompactMinus2176.nodes2188,NodeMinus34.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2176.p2189,GridMinus.atNode 2189,GridMinus.atNode 2190,NodeMinus34.w13,CompactMinus2176.checked2189,CompactMinus2176.small2189,CompactMinus2176.nodes2189,NodeMinus34.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2176.p2190,GridMinus.atNode 2190,GridMinus.atNode 2191,NodeMinus34.w14,CompactMinus2176.checked2190,CompactMinus2176.small2190,CompactMinus2176.nodes2190,NodeMinus34.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2176.p2191,GridMinus.atNode 2191,GridMinus.atNode 2192,NodeMinus34.w15,CompactMinus2176.checked2191,CompactMinus2176.small2191,CompactMinus2176.nodes2191,NodeMinus34.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2192.p2192,GridMinus.atNode 2192,GridMinus.atNode 2193,NodeMinus34.w16,CompactMinus2192.checked2192,CompactMinus2192.small2192,CompactMinus2192.nodes2192,NodeMinus34.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2192.p2193,GridMinus.atNode 2193,GridMinus.atNode 2194,NodeMinus34.w17,CompactMinus2192.checked2193,CompactMinus2192.small2193,CompactMinus2192.nodes2193,NodeMinus34.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2192.p2194,GridMinus.atNode 2194,GridMinus.atNode 2195,NodeMinus34.w18,CompactMinus2192.checked2194,CompactMinus2192.small2194,CompactMinus2192.nodes2194,NodeMinus34.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2192.p2195,GridMinus.atNode 2195,GridMinus.atNode 2196,NodeMinus34.w19,CompactMinus2192.checked2195,CompactMinus2192.small2195,CompactMinus2192.nodes2195,NodeMinus34.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2192.p2196,GridMinus.atNode 2196,GridMinus.atNode 2197,NodeMinus34.w20,CompactMinus2192.checked2196,CompactMinus2192.small2196,CompactMinus2192.nodes2196,NodeMinus34.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2192.p2197,GridMinus.atNode 2197,GridMinus.atNode 2198,NodeMinus34.w21,CompactMinus2192.checked2197,CompactMinus2192.small2197,CompactMinus2192.nodes2197,NodeMinus34.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2192.p2198,GridMinus.atNode 2198,GridMinus.atNode 2199,NodeMinus34.w22,CompactMinus2192.checked2198,CompactMinus2192.small2198,CompactMinus2192.nodes2198,NodeMinus34.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2192.p2199,GridMinus.atNode 2199,GridMinus.atNode 2200,NodeMinus34.w23,CompactMinus2192.checked2199,CompactMinus2192.small2199,CompactMinus2192.nodes2199,NodeMinus34.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2192.p2200,GridMinus.atNode 2200,GridMinus.atNode 2201,NodeMinus34.w24,CompactMinus2192.checked2200,CompactMinus2192.small2200,CompactMinus2192.nodes2200,NodeMinus34.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2192.p2201,GridMinus.atNode 2201,GridMinus.atNode 2202,NodeMinus34.w25,CompactMinus2192.checked2201,CompactMinus2192.small2201,CompactMinus2192.nodes2201,NodeMinus34.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2192.p2202,GridMinus.atNode 2202,GridMinus.atNode 2203,NodeMinus34.w26,CompactMinus2192.checked2202,CompactMinus2192.small2202,CompactMinus2192.nodes2202,NodeMinus34.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2192.p2203,GridMinus.atNode 2203,GridMinus.atNode 2204,NodeMinus34.w27,CompactMinus2192.checked2203,CompactMinus2192.small2203,CompactMinus2192.nodes2203,NodeMinus34.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2192.p2204,GridMinus.atNode 2204,GridMinus.atNode 2205,NodeMinus34.w28,CompactMinus2192.checked2204,CompactMinus2192.small2204,CompactMinus2192.nodes2204,NodeMinus34.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2192.p2205,GridMinus.atNode 2205,GridMinus.atNode 2206,NodeMinus34.w29,CompactMinus2192.checked2205,CompactMinus2192.small2205,CompactMinus2192.nodes2205,NodeMinus34.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2192.p2206,GridMinus.atNode 2206,GridMinus.atNode 2207,NodeMinus34.w30,CompactMinus2192.checked2206,CompactMinus2192.small2206,CompactMinus2192.nodes2206,NodeMinus34.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2192.p2207,GridMinus.atNode 2207,GridMinus.atNode 2208,NodeMinus34.w31,CompactMinus2192.checked2207,CompactMinus2192.small2207,CompactMinus2192.nodes2207,NodeMinus34.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2208.p2208,GridMinus.atNode 2208,GridMinus.atNode 2209,NodeMinus34.w32,CompactMinus2208.checked2208,CompactMinus2208.small2208,CompactMinus2208.nodes2208,NodeMinus34.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2208.p2209,GridMinus.atNode 2209,GridMinus.atNode 2210,NodeMinus34.w33,CompactMinus2208.checked2209,CompactMinus2208.small2209,CompactMinus2208.nodes2209,NodeMinus34.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2208.p2210,GridMinus.atNode 2210,GridMinus.atNode 2211,NodeMinus34.w34,CompactMinus2208.checked2210,CompactMinus2208.small2210,CompactMinus2208.nodes2210,NodeMinus34.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2208.p2211,GridMinus.atNode 2211,GridMinus.atNode 2212,NodeMinus34.w35,CompactMinus2208.checked2211,CompactMinus2208.small2211,CompactMinus2208.nodes2211,NodeMinus34.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2208.p2212,GridMinus.atNode 2212,GridMinus.atNode 2213,NodeMinus34.w36,CompactMinus2208.checked2212,CompactMinus2208.small2212,CompactMinus2208.nodes2212,NodeMinus34.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2208.p2213,GridMinus.atNode 2213,GridMinus.atNode 2214,NodeMinus34.w37,CompactMinus2208.checked2213,CompactMinus2208.small2213,CompactMinus2208.nodes2213,NodeMinus34.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2208.p2214,GridMinus.atNode 2214,GridMinus.atNode 2215,NodeMinus34.w38,CompactMinus2208.checked2214,CompactMinus2208.small2214,CompactMinus2208.nodes2214,NodeMinus34.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2208.p2215,GridMinus.atNode 2215,GridMinus.atNode 2216,NodeMinus34.w39,CompactMinus2208.checked2215,CompactMinus2208.small2215,CompactMinus2208.nodes2215,NodeMinus34.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2208.p2216,GridMinus.atNode 2216,GridMinus.atNode 2217,NodeMinus34.w40,CompactMinus2208.checked2216,CompactMinus2208.small2216,CompactMinus2208.nodes2216,NodeMinus34.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2208.p2217,GridMinus.atNode 2217,GridMinus.atNode 2218,NodeMinus34.w41,CompactMinus2208.checked2217,CompactMinus2208.small2217,CompactMinus2208.nodes2217,NodeMinus34.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2208.p2218,GridMinus.atNode 2218,GridMinus.atNode 2219,NodeMinus34.w42,CompactMinus2208.checked2218,CompactMinus2208.small2218,CompactMinus2208.nodes2218,NodeMinus34.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2208.p2219,GridMinus.atNode 2219,GridMinus.atNode 2220,NodeMinus34.w43,CompactMinus2208.checked2219,CompactMinus2208.small2219,CompactMinus2208.nodes2219,NodeMinus34.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2208.p2220,GridMinus.atNode 2220,GridMinus.atNode 2221,NodeMinus34.w44,CompactMinus2208.checked2220,CompactMinus2208.small2220,CompactMinus2208.nodes2220,NodeMinus34.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2208.p2221,GridMinus.atNode 2221,GridMinus.atNode 2222,NodeMinus34.w45,CompactMinus2208.checked2221,CompactMinus2208.small2221,CompactMinus2208.nodes2221,NodeMinus34.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2208.p2222,GridMinus.atNode 2222,GridMinus.atNode 2223,NodeMinus34.w46,CompactMinus2208.checked2222,CompactMinus2208.small2222,CompactMinus2208.nodes2222,NodeMinus34.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2208.p2223,GridMinus.atNode 2223,GridMinus.atNode 2224,NodeMinus34.w47,CompactMinus2208.checked2223,CompactMinus2208.small2223,CompactMinus2208.nodes2223,NodeMinus34.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2224.p2224,GridMinus.atNode 2224,GridMinus.atNode 2225,NodeMinus34.w48,CompactMinus2224.checked2224,CompactMinus2224.small2224,CompactMinus2224.nodes2224,NodeMinus34.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2224.p2225,GridMinus.atNode 2225,GridMinus.atNode 2226,NodeMinus34.w49,CompactMinus2224.checked2225,CompactMinus2224.small2225,CompactMinus2224.nodes2225,NodeMinus34.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2224.p2226,GridMinus.atNode 2226,GridMinus.atNode 2227,NodeMinus34.w50,CompactMinus2224.checked2226,CompactMinus2224.small2226,CompactMinus2224.nodes2226,NodeMinus34.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2224.p2227,GridMinus.atNode 2227,GridMinus.atNode 2228,NodeMinus34.w51,CompactMinus2224.checked2227,CompactMinus2224.small2227,CompactMinus2224.nodes2227,NodeMinus34.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2224.p2228,GridMinus.atNode 2228,GridMinus.atNode 2229,NodeMinus34.w52,CompactMinus2224.checked2228,CompactMinus2224.small2228,CompactMinus2224.nodes2228,NodeMinus34.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2224.p2229,GridMinus.atNode 2229,GridMinus.atNode 2230,NodeMinus34.w53,CompactMinus2224.checked2229,CompactMinus2224.small2229,CompactMinus2224.nodes2229,NodeMinus34.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2224.p2230,GridMinus.atNode 2230,GridMinus.atNode 2231,NodeMinus34.w54,CompactMinus2224.checked2230,CompactMinus2224.small2230,CompactMinus2224.nodes2230,NodeMinus34.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2224.p2231,GridMinus.atNode 2231,GridMinus.atNode 2232,NodeMinus34.w55,CompactMinus2224.checked2231,CompactMinus2224.small2231,CompactMinus2224.nodes2231,NodeMinus34.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2224.p2232,GridMinus.atNode 2232,GridMinus.atNode 2233,NodeMinus34.w56,CompactMinus2224.checked2232,CompactMinus2224.small2232,CompactMinus2224.nodes2232,NodeMinus34.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2224.p2233,GridMinus.atNode 2233,GridMinus.atNode 2234,NodeMinus34.w57,CompactMinus2224.checked2233,CompactMinus2224.small2233,CompactMinus2224.nodes2233,NodeMinus34.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2224.p2234,GridMinus.atNode 2234,GridMinus.atNode 2235,NodeMinus34.w58,CompactMinus2224.checked2234,CompactMinus2224.small2234,CompactMinus2224.nodes2234,NodeMinus34.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2224.p2235,GridMinus.atNode 2235,GridMinus.atNode 2236,NodeMinus34.w59,CompactMinus2224.checked2235,CompactMinus2224.small2235,CompactMinus2224.nodes2235,NodeMinus34.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2224.p2236,GridMinus.atNode 2236,GridMinus.atNode 2237,NodeMinus34.w60,CompactMinus2224.checked2236,CompactMinus2224.small2236,CompactMinus2224.nodes2236,NodeMinus34.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2224.p2237,GridMinus.atNode 2237,GridMinus.atNode 2238,NodeMinus34.w61,CompactMinus2224.checked2237,CompactMinus2224.small2237,CompactMinus2224.nodes2237,NodeMinus34.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2224.p2238,GridMinus.atNode 2238,GridMinus.atNode 2239,NodeMinus34.w62,CompactMinus2224.checked2238,CompactMinus2224.small2238,CompactMinus2224.nodes2238,NodeMinus34.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2224.p2239,GridMinus.atNode 2239,GridMinus.atNode 2240,NodeMinus34.w63,CompactMinus2224.checked2239,CompactMinus2224.small2239,CompactMinus2224.nodes2239,NodeMinus34.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (2176+j) ∧
    (atRow j).right=GridMinus.atNode (2176+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus34
