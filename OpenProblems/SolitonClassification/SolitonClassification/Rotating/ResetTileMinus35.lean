import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus2240
import SolitonClassification.Rotating.ResetPackedMinus2256
import SolitonClassification.Rotating.ResetPackedMinus2272
import SolitonClassification.Rotating.ResetPackedMinus2288
namespace SolitonClassification.Rotating.DyadicReset.TileMinus35
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2240.p2240,GridMinus.atNode 2240,GridMinus.atNode 2241,NodeMinus35.w0,CompactMinus2240.checked2240,CompactMinus2240.small2240,CompactMinus2240.nodes2240,NodeMinus35.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2240.p2241,GridMinus.atNode 2241,GridMinus.atNode 2242,NodeMinus35.w1,CompactMinus2240.checked2241,CompactMinus2240.small2241,CompactMinus2240.nodes2241,NodeMinus35.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2240.p2242,GridMinus.atNode 2242,GridMinus.atNode 2243,NodeMinus35.w2,CompactMinus2240.checked2242,CompactMinus2240.small2242,CompactMinus2240.nodes2242,NodeMinus35.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2240.p2243,GridMinus.atNode 2243,GridMinus.atNode 2244,NodeMinus35.w3,CompactMinus2240.checked2243,CompactMinus2240.small2243,CompactMinus2240.nodes2243,NodeMinus35.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2240.p2244,GridMinus.atNode 2244,GridMinus.atNode 2245,NodeMinus35.w4,CompactMinus2240.checked2244,CompactMinus2240.small2244,CompactMinus2240.nodes2244,NodeMinus35.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2240.p2245,GridMinus.atNode 2245,GridMinus.atNode 2246,NodeMinus35.w5,CompactMinus2240.checked2245,CompactMinus2240.small2245,CompactMinus2240.nodes2245,NodeMinus35.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2240.p2246,GridMinus.atNode 2246,GridMinus.atNode 2247,NodeMinus35.w6,CompactMinus2240.checked2246,CompactMinus2240.small2246,CompactMinus2240.nodes2246,NodeMinus35.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2240.p2247,GridMinus.atNode 2247,GridMinus.atNode 2248,NodeMinus35.w7,CompactMinus2240.checked2247,CompactMinus2240.small2247,CompactMinus2240.nodes2247,NodeMinus35.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2240.p2248,GridMinus.atNode 2248,GridMinus.atNode 2249,NodeMinus35.w8,CompactMinus2240.checked2248,CompactMinus2240.small2248,CompactMinus2240.nodes2248,NodeMinus35.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2240.p2249,GridMinus.atNode 2249,GridMinus.atNode 2250,NodeMinus35.w9,CompactMinus2240.checked2249,CompactMinus2240.small2249,CompactMinus2240.nodes2249,NodeMinus35.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2240.p2250,GridMinus.atNode 2250,GridMinus.atNode 2251,NodeMinus35.w10,CompactMinus2240.checked2250,CompactMinus2240.small2250,CompactMinus2240.nodes2250,NodeMinus35.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2240.p2251,GridMinus.atNode 2251,GridMinus.atNode 2252,NodeMinus35.w11,CompactMinus2240.checked2251,CompactMinus2240.small2251,CompactMinus2240.nodes2251,NodeMinus35.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2240.p2252,GridMinus.atNode 2252,GridMinus.atNode 2253,NodeMinus35.w12,CompactMinus2240.checked2252,CompactMinus2240.small2252,CompactMinus2240.nodes2252,NodeMinus35.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2240.p2253,GridMinus.atNode 2253,GridMinus.atNode 2254,NodeMinus35.w13,CompactMinus2240.checked2253,CompactMinus2240.small2253,CompactMinus2240.nodes2253,NodeMinus35.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2240.p2254,GridMinus.atNode 2254,GridMinus.atNode 2255,NodeMinus35.w14,CompactMinus2240.checked2254,CompactMinus2240.small2254,CompactMinus2240.nodes2254,NodeMinus35.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2240.p2255,GridMinus.atNode 2255,GridMinus.atNode 2256,NodeMinus35.w15,CompactMinus2240.checked2255,CompactMinus2240.small2255,CompactMinus2240.nodes2255,NodeMinus35.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2256.p2256,GridMinus.atNode 2256,GridMinus.atNode 2257,NodeMinus35.w16,CompactMinus2256.checked2256,CompactMinus2256.small2256,CompactMinus2256.nodes2256,NodeMinus35.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2256.p2257,GridMinus.atNode 2257,GridMinus.atNode 2258,NodeMinus35.w17,CompactMinus2256.checked2257,CompactMinus2256.small2257,CompactMinus2256.nodes2257,NodeMinus35.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2256.p2258,GridMinus.atNode 2258,GridMinus.atNode 2259,NodeMinus35.w18,CompactMinus2256.checked2258,CompactMinus2256.small2258,CompactMinus2256.nodes2258,NodeMinus35.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2256.p2259,GridMinus.atNode 2259,GridMinus.atNode 2260,NodeMinus35.w19,CompactMinus2256.checked2259,CompactMinus2256.small2259,CompactMinus2256.nodes2259,NodeMinus35.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2256.p2260,GridMinus.atNode 2260,GridMinus.atNode 2261,NodeMinus35.w20,CompactMinus2256.checked2260,CompactMinus2256.small2260,CompactMinus2256.nodes2260,NodeMinus35.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2256.p2261,GridMinus.atNode 2261,GridMinus.atNode 2262,NodeMinus35.w21,CompactMinus2256.checked2261,CompactMinus2256.small2261,CompactMinus2256.nodes2261,NodeMinus35.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2256.p2262,GridMinus.atNode 2262,GridMinus.atNode 2263,NodeMinus35.w22,CompactMinus2256.checked2262,CompactMinus2256.small2262,CompactMinus2256.nodes2262,NodeMinus35.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2256.p2263,GridMinus.atNode 2263,GridMinus.atNode 2264,NodeMinus35.w23,CompactMinus2256.checked2263,CompactMinus2256.small2263,CompactMinus2256.nodes2263,NodeMinus35.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2256.p2264,GridMinus.atNode 2264,GridMinus.atNode 2265,NodeMinus35.w24,CompactMinus2256.checked2264,CompactMinus2256.small2264,CompactMinus2256.nodes2264,NodeMinus35.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2256.p2265,GridMinus.atNode 2265,GridMinus.atNode 2266,NodeMinus35.w25,CompactMinus2256.checked2265,CompactMinus2256.small2265,CompactMinus2256.nodes2265,NodeMinus35.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2256.p2266,GridMinus.atNode 2266,GridMinus.atNode 2267,NodeMinus35.w26,CompactMinus2256.checked2266,CompactMinus2256.small2266,CompactMinus2256.nodes2266,NodeMinus35.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2256.p2267,GridMinus.atNode 2267,GridMinus.atNode 2268,NodeMinus35.w27,CompactMinus2256.checked2267,CompactMinus2256.small2267,CompactMinus2256.nodes2267,NodeMinus35.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2256.p2268,GridMinus.atNode 2268,GridMinus.atNode 2269,NodeMinus35.w28,CompactMinus2256.checked2268,CompactMinus2256.small2268,CompactMinus2256.nodes2268,NodeMinus35.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2256.p2269,GridMinus.atNode 2269,GridMinus.atNode 2270,NodeMinus35.w29,CompactMinus2256.checked2269,CompactMinus2256.small2269,CompactMinus2256.nodes2269,NodeMinus35.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2256.p2270,GridMinus.atNode 2270,GridMinus.atNode 2271,NodeMinus35.w30,CompactMinus2256.checked2270,CompactMinus2256.small2270,CompactMinus2256.nodes2270,NodeMinus35.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2256.p2271,GridMinus.atNode 2271,GridMinus.atNode 2272,NodeMinus35.w31,CompactMinus2256.checked2271,CompactMinus2256.small2271,CompactMinus2256.nodes2271,NodeMinus35.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2272.p2272,GridMinus.atNode 2272,GridMinus.atNode 2273,NodeMinus35.w32,CompactMinus2272.checked2272,CompactMinus2272.small2272,CompactMinus2272.nodes2272,NodeMinus35.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2272.p2273,GridMinus.atNode 2273,GridMinus.atNode 2274,NodeMinus35.w33,CompactMinus2272.checked2273,CompactMinus2272.small2273,CompactMinus2272.nodes2273,NodeMinus35.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2272.p2274,GridMinus.atNode 2274,GridMinus.atNode 2275,NodeMinus35.w34,CompactMinus2272.checked2274,CompactMinus2272.small2274,CompactMinus2272.nodes2274,NodeMinus35.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2272.p2275,GridMinus.atNode 2275,GridMinus.atNode 2276,NodeMinus35.w35,CompactMinus2272.checked2275,CompactMinus2272.small2275,CompactMinus2272.nodes2275,NodeMinus35.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2272.p2276,GridMinus.atNode 2276,GridMinus.atNode 2277,NodeMinus35.w36,CompactMinus2272.checked2276,CompactMinus2272.small2276,CompactMinus2272.nodes2276,NodeMinus35.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2272.p2277,GridMinus.atNode 2277,GridMinus.atNode 2278,NodeMinus35.w37,CompactMinus2272.checked2277,CompactMinus2272.small2277,CompactMinus2272.nodes2277,NodeMinus35.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2272.p2278,GridMinus.atNode 2278,GridMinus.atNode 2279,NodeMinus35.w38,CompactMinus2272.checked2278,CompactMinus2272.small2278,CompactMinus2272.nodes2278,NodeMinus35.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2272.p2279,GridMinus.atNode 2279,GridMinus.atNode 2280,NodeMinus35.w39,CompactMinus2272.checked2279,CompactMinus2272.small2279,CompactMinus2272.nodes2279,NodeMinus35.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2272.p2280,GridMinus.atNode 2280,GridMinus.atNode 2281,NodeMinus35.w40,CompactMinus2272.checked2280,CompactMinus2272.small2280,CompactMinus2272.nodes2280,NodeMinus35.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2272.p2281,GridMinus.atNode 2281,GridMinus.atNode 2282,NodeMinus35.w41,CompactMinus2272.checked2281,CompactMinus2272.small2281,CompactMinus2272.nodes2281,NodeMinus35.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2272.p2282,GridMinus.atNode 2282,GridMinus.atNode 2283,NodeMinus35.w42,CompactMinus2272.checked2282,CompactMinus2272.small2282,CompactMinus2272.nodes2282,NodeMinus35.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2272.p2283,GridMinus.atNode 2283,GridMinus.atNode 2284,NodeMinus35.w43,CompactMinus2272.checked2283,CompactMinus2272.small2283,CompactMinus2272.nodes2283,NodeMinus35.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2272.p2284,GridMinus.atNode 2284,GridMinus.atNode 2285,NodeMinus35.w44,CompactMinus2272.checked2284,CompactMinus2272.small2284,CompactMinus2272.nodes2284,NodeMinus35.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2272.p2285,GridMinus.atNode 2285,GridMinus.atNode 2286,NodeMinus35.w45,CompactMinus2272.checked2285,CompactMinus2272.small2285,CompactMinus2272.nodes2285,NodeMinus35.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2272.p2286,GridMinus.atNode 2286,GridMinus.atNode 2287,NodeMinus35.w46,CompactMinus2272.checked2286,CompactMinus2272.small2286,CompactMinus2272.nodes2286,NodeMinus35.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2272.p2287,GridMinus.atNode 2287,GridMinus.atNode 2288,NodeMinus35.w47,CompactMinus2272.checked2287,CompactMinus2272.small2287,CompactMinus2272.nodes2287,NodeMinus35.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2288.p2288,GridMinus.atNode 2288,GridMinus.atNode 2289,NodeMinus35.w48,CompactMinus2288.checked2288,CompactMinus2288.small2288,CompactMinus2288.nodes2288,NodeMinus35.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2288.p2289,GridMinus.atNode 2289,GridMinus.atNode 2290,NodeMinus35.w49,CompactMinus2288.checked2289,CompactMinus2288.small2289,CompactMinus2288.nodes2289,NodeMinus35.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2288.p2290,GridMinus.atNode 2290,GridMinus.atNode 2291,NodeMinus35.w50,CompactMinus2288.checked2290,CompactMinus2288.small2290,CompactMinus2288.nodes2290,NodeMinus35.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2288.p2291,GridMinus.atNode 2291,GridMinus.atNode 2292,NodeMinus35.w51,CompactMinus2288.checked2291,CompactMinus2288.small2291,CompactMinus2288.nodes2291,NodeMinus35.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2288.p2292,GridMinus.atNode 2292,GridMinus.atNode 2293,NodeMinus35.w52,CompactMinus2288.checked2292,CompactMinus2288.small2292,CompactMinus2288.nodes2292,NodeMinus35.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2288.p2293,GridMinus.atNode 2293,GridMinus.atNode 2294,NodeMinus35.w53,CompactMinus2288.checked2293,CompactMinus2288.small2293,CompactMinus2288.nodes2293,NodeMinus35.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2288.p2294,GridMinus.atNode 2294,GridMinus.atNode 2295,NodeMinus35.w54,CompactMinus2288.checked2294,CompactMinus2288.small2294,CompactMinus2288.nodes2294,NodeMinus35.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2288.p2295,GridMinus.atNode 2295,GridMinus.atNode 2296,NodeMinus35.w55,CompactMinus2288.checked2295,CompactMinus2288.small2295,CompactMinus2288.nodes2295,NodeMinus35.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2288.p2296,GridMinus.atNode 2296,GridMinus.atNode 2297,NodeMinus35.w56,CompactMinus2288.checked2296,CompactMinus2288.small2296,CompactMinus2288.nodes2296,NodeMinus35.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2288.p2297,GridMinus.atNode 2297,GridMinus.atNode 2298,NodeMinus35.w57,CompactMinus2288.checked2297,CompactMinus2288.small2297,CompactMinus2288.nodes2297,NodeMinus35.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2288.p2298,GridMinus.atNode 2298,GridMinus.atNode 2299,NodeMinus35.w58,CompactMinus2288.checked2298,CompactMinus2288.small2298,CompactMinus2288.nodes2298,NodeMinus35.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2288.p2299,GridMinus.atNode 2299,GridMinus.atNode 2300,NodeMinus35.w59,CompactMinus2288.checked2299,CompactMinus2288.small2299,CompactMinus2288.nodes2299,NodeMinus35.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2288.p2300,GridMinus.atNode 2300,GridMinus.atNode 2301,NodeMinus35.w60,CompactMinus2288.checked2300,CompactMinus2288.small2300,CompactMinus2288.nodes2300,NodeMinus35.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2288.p2301,GridMinus.atNode 2301,GridMinus.atNode 2302,NodeMinus35.w61,CompactMinus2288.checked2301,CompactMinus2288.small2301,CompactMinus2288.nodes2301,NodeMinus35.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2288.p2302,GridMinus.atNode 2302,GridMinus.atNode 2303,NodeMinus35.w62,CompactMinus2288.checked2302,CompactMinus2288.small2302,CompactMinus2288.nodes2302,NodeMinus35.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2288.p2303,GridMinus.atNode 2303,GridMinus.atNode 2304,NodeMinus35.w63,CompactMinus2288.checked2303,CompactMinus2288.small2303,CompactMinus2288.nodes2303,NodeMinus35.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (2240+j) ∧
    (atRow j).right=GridMinus.atNode (2240+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus35
