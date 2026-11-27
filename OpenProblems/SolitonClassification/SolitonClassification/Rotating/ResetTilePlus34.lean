import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus2176
import SolitonClassification.Rotating.ResetPackedPlus2192
import SolitonClassification.Rotating.ResetPackedPlus2208
import SolitonClassification.Rotating.ResetPackedPlus2224
namespace SolitonClassification.Rotating.DyadicReset.TilePlus34
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus2176.p2176,GridPlus.atNode 2176,GridPlus.atNode 2177,NodePlus34.w0,CompactPlus2176.checked2176,CompactPlus2176.small2176,CompactPlus2176.nodes2176,NodePlus34.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus2176.p2177,GridPlus.atNode 2177,GridPlus.atNode 2178,NodePlus34.w1,CompactPlus2176.checked2177,CompactPlus2176.small2177,CompactPlus2176.nodes2177,NodePlus34.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus2176.p2178,GridPlus.atNode 2178,GridPlus.atNode 2179,NodePlus34.w2,CompactPlus2176.checked2178,CompactPlus2176.small2178,CompactPlus2176.nodes2178,NodePlus34.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus2176.p2179,GridPlus.atNode 2179,GridPlus.atNode 2180,NodePlus34.w3,CompactPlus2176.checked2179,CompactPlus2176.small2179,CompactPlus2176.nodes2179,NodePlus34.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus2176.p2180,GridPlus.atNode 2180,GridPlus.atNode 2181,NodePlus34.w4,CompactPlus2176.checked2180,CompactPlus2176.small2180,CompactPlus2176.nodes2180,NodePlus34.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus2176.p2181,GridPlus.atNode 2181,GridPlus.atNode 2182,NodePlus34.w5,CompactPlus2176.checked2181,CompactPlus2176.small2181,CompactPlus2176.nodes2181,NodePlus34.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus2176.p2182,GridPlus.atNode 2182,GridPlus.atNode 2183,NodePlus34.w6,CompactPlus2176.checked2182,CompactPlus2176.small2182,CompactPlus2176.nodes2182,NodePlus34.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus2176.p2183,GridPlus.atNode 2183,GridPlus.atNode 2184,NodePlus34.w7,CompactPlus2176.checked2183,CompactPlus2176.small2183,CompactPlus2176.nodes2183,NodePlus34.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus2176.p2184,GridPlus.atNode 2184,GridPlus.atNode 2185,NodePlus34.w8,CompactPlus2176.checked2184,CompactPlus2176.small2184,CompactPlus2176.nodes2184,NodePlus34.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus2176.p2185,GridPlus.atNode 2185,GridPlus.atNode 2186,NodePlus34.w9,CompactPlus2176.checked2185,CompactPlus2176.small2185,CompactPlus2176.nodes2185,NodePlus34.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus2176.p2186,GridPlus.atNode 2186,GridPlus.atNode 2187,NodePlus34.w10,CompactPlus2176.checked2186,CompactPlus2176.small2186,CompactPlus2176.nodes2186,NodePlus34.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus2176.p2187,GridPlus.atNode 2187,GridPlus.atNode 2188,NodePlus34.w11,CompactPlus2176.checked2187,CompactPlus2176.small2187,CompactPlus2176.nodes2187,NodePlus34.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus2176.p2188,GridPlus.atNode 2188,GridPlus.atNode 2189,NodePlus34.w12,CompactPlus2176.checked2188,CompactPlus2176.small2188,CompactPlus2176.nodes2188,NodePlus34.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus2176.p2189,GridPlus.atNode 2189,GridPlus.atNode 2190,NodePlus34.w13,CompactPlus2176.checked2189,CompactPlus2176.small2189,CompactPlus2176.nodes2189,NodePlus34.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus2176.p2190,GridPlus.atNode 2190,GridPlus.atNode 2191,NodePlus34.w14,CompactPlus2176.checked2190,CompactPlus2176.small2190,CompactPlus2176.nodes2190,NodePlus34.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus2176.p2191,GridPlus.atNode 2191,GridPlus.atNode 2192,NodePlus34.w15,CompactPlus2176.checked2191,CompactPlus2176.small2191,CompactPlus2176.nodes2191,NodePlus34.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus2192.p2192,GridPlus.atNode 2192,GridPlus.atNode 2193,NodePlus34.w16,CompactPlus2192.checked2192,CompactPlus2192.small2192,CompactPlus2192.nodes2192,NodePlus34.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus2192.p2193,GridPlus.atNode 2193,GridPlus.atNode 2194,NodePlus34.w17,CompactPlus2192.checked2193,CompactPlus2192.small2193,CompactPlus2192.nodes2193,NodePlus34.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus2192.p2194,GridPlus.atNode 2194,GridPlus.atNode 2195,NodePlus34.w18,CompactPlus2192.checked2194,CompactPlus2192.small2194,CompactPlus2192.nodes2194,NodePlus34.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus2192.p2195,GridPlus.atNode 2195,GridPlus.atNode 2196,NodePlus34.w19,CompactPlus2192.checked2195,CompactPlus2192.small2195,CompactPlus2192.nodes2195,NodePlus34.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus2192.p2196,GridPlus.atNode 2196,GridPlus.atNode 2197,NodePlus34.w20,CompactPlus2192.checked2196,CompactPlus2192.small2196,CompactPlus2192.nodes2196,NodePlus34.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus2192.p2197,GridPlus.atNode 2197,GridPlus.atNode 2198,NodePlus34.w21,CompactPlus2192.checked2197,CompactPlus2192.small2197,CompactPlus2192.nodes2197,NodePlus34.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus2192.p2198,GridPlus.atNode 2198,GridPlus.atNode 2199,NodePlus34.w22,CompactPlus2192.checked2198,CompactPlus2192.small2198,CompactPlus2192.nodes2198,NodePlus34.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus2192.p2199,GridPlus.atNode 2199,GridPlus.atNode 2200,NodePlus34.w23,CompactPlus2192.checked2199,CompactPlus2192.small2199,CompactPlus2192.nodes2199,NodePlus34.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus2192.p2200,GridPlus.atNode 2200,GridPlus.atNode 2201,NodePlus34.w24,CompactPlus2192.checked2200,CompactPlus2192.small2200,CompactPlus2192.nodes2200,NodePlus34.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus2192.p2201,GridPlus.atNode 2201,GridPlus.atNode 2202,NodePlus34.w25,CompactPlus2192.checked2201,CompactPlus2192.small2201,CompactPlus2192.nodes2201,NodePlus34.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus2192.p2202,GridPlus.atNode 2202,GridPlus.atNode 2203,NodePlus34.w26,CompactPlus2192.checked2202,CompactPlus2192.small2202,CompactPlus2192.nodes2202,NodePlus34.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus2192.p2203,GridPlus.atNode 2203,GridPlus.atNode 2204,NodePlus34.w27,CompactPlus2192.checked2203,CompactPlus2192.small2203,CompactPlus2192.nodes2203,NodePlus34.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus2192.p2204,GridPlus.atNode 2204,GridPlus.atNode 2205,NodePlus34.w28,CompactPlus2192.checked2204,CompactPlus2192.small2204,CompactPlus2192.nodes2204,NodePlus34.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus2192.p2205,GridPlus.atNode 2205,GridPlus.atNode 2206,NodePlus34.w29,CompactPlus2192.checked2205,CompactPlus2192.small2205,CompactPlus2192.nodes2205,NodePlus34.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus2192.p2206,GridPlus.atNode 2206,GridPlus.atNode 2207,NodePlus34.w30,CompactPlus2192.checked2206,CompactPlus2192.small2206,CompactPlus2192.nodes2206,NodePlus34.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus2192.p2207,GridPlus.atNode 2207,GridPlus.atNode 2208,NodePlus34.w31,CompactPlus2192.checked2207,CompactPlus2192.small2207,CompactPlus2192.nodes2207,NodePlus34.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus2208.p2208,GridPlus.atNode 2208,GridPlus.atNode 2209,NodePlus34.w32,CompactPlus2208.checked2208,CompactPlus2208.small2208,CompactPlus2208.nodes2208,NodePlus34.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus2208.p2209,GridPlus.atNode 2209,GridPlus.atNode 2210,NodePlus34.w33,CompactPlus2208.checked2209,CompactPlus2208.small2209,CompactPlus2208.nodes2209,NodePlus34.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus2208.p2210,GridPlus.atNode 2210,GridPlus.atNode 2211,NodePlus34.w34,CompactPlus2208.checked2210,CompactPlus2208.small2210,CompactPlus2208.nodes2210,NodePlus34.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus2208.p2211,GridPlus.atNode 2211,GridPlus.atNode 2212,NodePlus34.w35,CompactPlus2208.checked2211,CompactPlus2208.small2211,CompactPlus2208.nodes2211,NodePlus34.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus2208.p2212,GridPlus.atNode 2212,GridPlus.atNode 2213,NodePlus34.w36,CompactPlus2208.checked2212,CompactPlus2208.small2212,CompactPlus2208.nodes2212,NodePlus34.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus2208.p2213,GridPlus.atNode 2213,GridPlus.atNode 2214,NodePlus34.w37,CompactPlus2208.checked2213,CompactPlus2208.small2213,CompactPlus2208.nodes2213,NodePlus34.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus2208.p2214,GridPlus.atNode 2214,GridPlus.atNode 2215,NodePlus34.w38,CompactPlus2208.checked2214,CompactPlus2208.small2214,CompactPlus2208.nodes2214,NodePlus34.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus2208.p2215,GridPlus.atNode 2215,GridPlus.atNode 2216,NodePlus34.w39,CompactPlus2208.checked2215,CompactPlus2208.small2215,CompactPlus2208.nodes2215,NodePlus34.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus2208.p2216,GridPlus.atNode 2216,GridPlus.atNode 2217,NodePlus34.w40,CompactPlus2208.checked2216,CompactPlus2208.small2216,CompactPlus2208.nodes2216,NodePlus34.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus2208.p2217,GridPlus.atNode 2217,GridPlus.atNode 2218,NodePlus34.w41,CompactPlus2208.checked2217,CompactPlus2208.small2217,CompactPlus2208.nodes2217,NodePlus34.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus2208.p2218,GridPlus.atNode 2218,GridPlus.atNode 2219,NodePlus34.w42,CompactPlus2208.checked2218,CompactPlus2208.small2218,CompactPlus2208.nodes2218,NodePlus34.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus2208.p2219,GridPlus.atNode 2219,GridPlus.atNode 2220,NodePlus34.w43,CompactPlus2208.checked2219,CompactPlus2208.small2219,CompactPlus2208.nodes2219,NodePlus34.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus2208.p2220,GridPlus.atNode 2220,GridPlus.atNode 2221,NodePlus34.w44,CompactPlus2208.checked2220,CompactPlus2208.small2220,CompactPlus2208.nodes2220,NodePlus34.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus2208.p2221,GridPlus.atNode 2221,GridPlus.atNode 2222,NodePlus34.w45,CompactPlus2208.checked2221,CompactPlus2208.small2221,CompactPlus2208.nodes2221,NodePlus34.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus2208.p2222,GridPlus.atNode 2222,GridPlus.atNode 2223,NodePlus34.w46,CompactPlus2208.checked2222,CompactPlus2208.small2222,CompactPlus2208.nodes2222,NodePlus34.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus2208.p2223,GridPlus.atNode 2223,GridPlus.atNode 2224,NodePlus34.w47,CompactPlus2208.checked2223,CompactPlus2208.small2223,CompactPlus2208.nodes2223,NodePlus34.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus2224.p2224,GridPlus.atNode 2224,GridPlus.atNode 2225,NodePlus34.w48,CompactPlus2224.checked2224,CompactPlus2224.small2224,CompactPlus2224.nodes2224,NodePlus34.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus2224.p2225,GridPlus.atNode 2225,GridPlus.atNode 2226,NodePlus34.w49,CompactPlus2224.checked2225,CompactPlus2224.small2225,CompactPlus2224.nodes2225,NodePlus34.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus2224.p2226,GridPlus.atNode 2226,GridPlus.atNode 2227,NodePlus34.w50,CompactPlus2224.checked2226,CompactPlus2224.small2226,CompactPlus2224.nodes2226,NodePlus34.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus2224.p2227,GridPlus.atNode 2227,GridPlus.atNode 2228,NodePlus34.w51,CompactPlus2224.checked2227,CompactPlus2224.small2227,CompactPlus2224.nodes2227,NodePlus34.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus2224.p2228,GridPlus.atNode 2228,GridPlus.atNode 2229,NodePlus34.w52,CompactPlus2224.checked2228,CompactPlus2224.small2228,CompactPlus2224.nodes2228,NodePlus34.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus2224.p2229,GridPlus.atNode 2229,GridPlus.atNode 2230,NodePlus34.w53,CompactPlus2224.checked2229,CompactPlus2224.small2229,CompactPlus2224.nodes2229,NodePlus34.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus2224.p2230,GridPlus.atNode 2230,GridPlus.atNode 2231,NodePlus34.w54,CompactPlus2224.checked2230,CompactPlus2224.small2230,CompactPlus2224.nodes2230,NodePlus34.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus2224.p2231,GridPlus.atNode 2231,GridPlus.atNode 2232,NodePlus34.w55,CompactPlus2224.checked2231,CompactPlus2224.small2231,CompactPlus2224.nodes2231,NodePlus34.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus2224.p2232,GridPlus.atNode 2232,GridPlus.atNode 2233,NodePlus34.w56,CompactPlus2224.checked2232,CompactPlus2224.small2232,CompactPlus2224.nodes2232,NodePlus34.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus2224.p2233,GridPlus.atNode 2233,GridPlus.atNode 2234,NodePlus34.w57,CompactPlus2224.checked2233,CompactPlus2224.small2233,CompactPlus2224.nodes2233,NodePlus34.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus2224.p2234,GridPlus.atNode 2234,GridPlus.atNode 2235,NodePlus34.w58,CompactPlus2224.checked2234,CompactPlus2224.small2234,CompactPlus2224.nodes2234,NodePlus34.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus2224.p2235,GridPlus.atNode 2235,GridPlus.atNode 2236,NodePlus34.w59,CompactPlus2224.checked2235,CompactPlus2224.small2235,CompactPlus2224.nodes2235,NodePlus34.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus2224.p2236,GridPlus.atNode 2236,GridPlus.atNode 2237,NodePlus34.w60,CompactPlus2224.checked2236,CompactPlus2224.small2236,CompactPlus2224.nodes2236,NodePlus34.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus2224.p2237,GridPlus.atNode 2237,GridPlus.atNode 2238,NodePlus34.w61,CompactPlus2224.checked2237,CompactPlus2224.small2237,CompactPlus2224.nodes2237,NodePlus34.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus2224.p2238,GridPlus.atNode 2238,GridPlus.atNode 2239,NodePlus34.w62,CompactPlus2224.checked2238,CompactPlus2224.small2238,CompactPlus2224.nodes2238,NodePlus34.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus2224.p2239,GridPlus.atNode 2239,GridPlus.atNode 2240,NodePlus34.w63,CompactPlus2224.checked2239,CompactPlus2224.small2239,CompactPlus2224.nodes2239,NodePlus34.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (2176+j) ∧
    (atRow j).right=GridPlus.atNode (2176+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus34
