import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus2240
import SolitonClassification.Rotating.ResetPackedPlus2256
import SolitonClassification.Rotating.ResetPackedPlus2272
import SolitonClassification.Rotating.ResetPackedPlus2288
namespace SolitonClassification.Rotating.DyadicReset.TilePlus35
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus2240.p2240,GridPlus.atNode 2240,GridPlus.atNode 2241,NodePlus35.w0,CompactPlus2240.checked2240,CompactPlus2240.small2240,CompactPlus2240.nodes2240,NodePlus35.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus2240.p2241,GridPlus.atNode 2241,GridPlus.atNode 2242,NodePlus35.w1,CompactPlus2240.checked2241,CompactPlus2240.small2241,CompactPlus2240.nodes2241,NodePlus35.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus2240.p2242,GridPlus.atNode 2242,GridPlus.atNode 2243,NodePlus35.w2,CompactPlus2240.checked2242,CompactPlus2240.small2242,CompactPlus2240.nodes2242,NodePlus35.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus2240.p2243,GridPlus.atNode 2243,GridPlus.atNode 2244,NodePlus35.w3,CompactPlus2240.checked2243,CompactPlus2240.small2243,CompactPlus2240.nodes2243,NodePlus35.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus2240.p2244,GridPlus.atNode 2244,GridPlus.atNode 2245,NodePlus35.w4,CompactPlus2240.checked2244,CompactPlus2240.small2244,CompactPlus2240.nodes2244,NodePlus35.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus2240.p2245,GridPlus.atNode 2245,GridPlus.atNode 2246,NodePlus35.w5,CompactPlus2240.checked2245,CompactPlus2240.small2245,CompactPlus2240.nodes2245,NodePlus35.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus2240.p2246,GridPlus.atNode 2246,GridPlus.atNode 2247,NodePlus35.w6,CompactPlus2240.checked2246,CompactPlus2240.small2246,CompactPlus2240.nodes2246,NodePlus35.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus2240.p2247,GridPlus.atNode 2247,GridPlus.atNode 2248,NodePlus35.w7,CompactPlus2240.checked2247,CompactPlus2240.small2247,CompactPlus2240.nodes2247,NodePlus35.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus2240.p2248,GridPlus.atNode 2248,GridPlus.atNode 2249,NodePlus35.w8,CompactPlus2240.checked2248,CompactPlus2240.small2248,CompactPlus2240.nodes2248,NodePlus35.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus2240.p2249,GridPlus.atNode 2249,GridPlus.atNode 2250,NodePlus35.w9,CompactPlus2240.checked2249,CompactPlus2240.small2249,CompactPlus2240.nodes2249,NodePlus35.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus2240.p2250,GridPlus.atNode 2250,GridPlus.atNode 2251,NodePlus35.w10,CompactPlus2240.checked2250,CompactPlus2240.small2250,CompactPlus2240.nodes2250,NodePlus35.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus2240.p2251,GridPlus.atNode 2251,GridPlus.atNode 2252,NodePlus35.w11,CompactPlus2240.checked2251,CompactPlus2240.small2251,CompactPlus2240.nodes2251,NodePlus35.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus2240.p2252,GridPlus.atNode 2252,GridPlus.atNode 2253,NodePlus35.w12,CompactPlus2240.checked2252,CompactPlus2240.small2252,CompactPlus2240.nodes2252,NodePlus35.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus2240.p2253,GridPlus.atNode 2253,GridPlus.atNode 2254,NodePlus35.w13,CompactPlus2240.checked2253,CompactPlus2240.small2253,CompactPlus2240.nodes2253,NodePlus35.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus2240.p2254,GridPlus.atNode 2254,GridPlus.atNode 2255,NodePlus35.w14,CompactPlus2240.checked2254,CompactPlus2240.small2254,CompactPlus2240.nodes2254,NodePlus35.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus2240.p2255,GridPlus.atNode 2255,GridPlus.atNode 2256,NodePlus35.w15,CompactPlus2240.checked2255,CompactPlus2240.small2255,CompactPlus2240.nodes2255,NodePlus35.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus2256.p2256,GridPlus.atNode 2256,GridPlus.atNode 2257,NodePlus35.w16,CompactPlus2256.checked2256,CompactPlus2256.small2256,CompactPlus2256.nodes2256,NodePlus35.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus2256.p2257,GridPlus.atNode 2257,GridPlus.atNode 2258,NodePlus35.w17,CompactPlus2256.checked2257,CompactPlus2256.small2257,CompactPlus2256.nodes2257,NodePlus35.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus2256.p2258,GridPlus.atNode 2258,GridPlus.atNode 2259,NodePlus35.w18,CompactPlus2256.checked2258,CompactPlus2256.small2258,CompactPlus2256.nodes2258,NodePlus35.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus2256.p2259,GridPlus.atNode 2259,GridPlus.atNode 2260,NodePlus35.w19,CompactPlus2256.checked2259,CompactPlus2256.small2259,CompactPlus2256.nodes2259,NodePlus35.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus2256.p2260,GridPlus.atNode 2260,GridPlus.atNode 2261,NodePlus35.w20,CompactPlus2256.checked2260,CompactPlus2256.small2260,CompactPlus2256.nodes2260,NodePlus35.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus2256.p2261,GridPlus.atNode 2261,GridPlus.atNode 2262,NodePlus35.w21,CompactPlus2256.checked2261,CompactPlus2256.small2261,CompactPlus2256.nodes2261,NodePlus35.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus2256.p2262,GridPlus.atNode 2262,GridPlus.atNode 2263,NodePlus35.w22,CompactPlus2256.checked2262,CompactPlus2256.small2262,CompactPlus2256.nodes2262,NodePlus35.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus2256.p2263,GridPlus.atNode 2263,GridPlus.atNode 2264,NodePlus35.w23,CompactPlus2256.checked2263,CompactPlus2256.small2263,CompactPlus2256.nodes2263,NodePlus35.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus2256.p2264,GridPlus.atNode 2264,GridPlus.atNode 2265,NodePlus35.w24,CompactPlus2256.checked2264,CompactPlus2256.small2264,CompactPlus2256.nodes2264,NodePlus35.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus2256.p2265,GridPlus.atNode 2265,GridPlus.atNode 2266,NodePlus35.w25,CompactPlus2256.checked2265,CompactPlus2256.small2265,CompactPlus2256.nodes2265,NodePlus35.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus2256.p2266,GridPlus.atNode 2266,GridPlus.atNode 2267,NodePlus35.w26,CompactPlus2256.checked2266,CompactPlus2256.small2266,CompactPlus2256.nodes2266,NodePlus35.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus2256.p2267,GridPlus.atNode 2267,GridPlus.atNode 2268,NodePlus35.w27,CompactPlus2256.checked2267,CompactPlus2256.small2267,CompactPlus2256.nodes2267,NodePlus35.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus2256.p2268,GridPlus.atNode 2268,GridPlus.atNode 2269,NodePlus35.w28,CompactPlus2256.checked2268,CompactPlus2256.small2268,CompactPlus2256.nodes2268,NodePlus35.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus2256.p2269,GridPlus.atNode 2269,GridPlus.atNode 2270,NodePlus35.w29,CompactPlus2256.checked2269,CompactPlus2256.small2269,CompactPlus2256.nodes2269,NodePlus35.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus2256.p2270,GridPlus.atNode 2270,GridPlus.atNode 2271,NodePlus35.w30,CompactPlus2256.checked2270,CompactPlus2256.small2270,CompactPlus2256.nodes2270,NodePlus35.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus2256.p2271,GridPlus.atNode 2271,GridPlus.atNode 2272,NodePlus35.w31,CompactPlus2256.checked2271,CompactPlus2256.small2271,CompactPlus2256.nodes2271,NodePlus35.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus2272.p2272,GridPlus.atNode 2272,GridPlus.atNode 2273,NodePlus35.w32,CompactPlus2272.checked2272,CompactPlus2272.small2272,CompactPlus2272.nodes2272,NodePlus35.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus2272.p2273,GridPlus.atNode 2273,GridPlus.atNode 2274,NodePlus35.w33,CompactPlus2272.checked2273,CompactPlus2272.small2273,CompactPlus2272.nodes2273,NodePlus35.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus2272.p2274,GridPlus.atNode 2274,GridPlus.atNode 2275,NodePlus35.w34,CompactPlus2272.checked2274,CompactPlus2272.small2274,CompactPlus2272.nodes2274,NodePlus35.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus2272.p2275,GridPlus.atNode 2275,GridPlus.atNode 2276,NodePlus35.w35,CompactPlus2272.checked2275,CompactPlus2272.small2275,CompactPlus2272.nodes2275,NodePlus35.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus2272.p2276,GridPlus.atNode 2276,GridPlus.atNode 2277,NodePlus35.w36,CompactPlus2272.checked2276,CompactPlus2272.small2276,CompactPlus2272.nodes2276,NodePlus35.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus2272.p2277,GridPlus.atNode 2277,GridPlus.atNode 2278,NodePlus35.w37,CompactPlus2272.checked2277,CompactPlus2272.small2277,CompactPlus2272.nodes2277,NodePlus35.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus2272.p2278,GridPlus.atNode 2278,GridPlus.atNode 2279,NodePlus35.w38,CompactPlus2272.checked2278,CompactPlus2272.small2278,CompactPlus2272.nodes2278,NodePlus35.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus2272.p2279,GridPlus.atNode 2279,GridPlus.atNode 2280,NodePlus35.w39,CompactPlus2272.checked2279,CompactPlus2272.small2279,CompactPlus2272.nodes2279,NodePlus35.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus2272.p2280,GridPlus.atNode 2280,GridPlus.atNode 2281,NodePlus35.w40,CompactPlus2272.checked2280,CompactPlus2272.small2280,CompactPlus2272.nodes2280,NodePlus35.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus2272.p2281,GridPlus.atNode 2281,GridPlus.atNode 2282,NodePlus35.w41,CompactPlus2272.checked2281,CompactPlus2272.small2281,CompactPlus2272.nodes2281,NodePlus35.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus2272.p2282,GridPlus.atNode 2282,GridPlus.atNode 2283,NodePlus35.w42,CompactPlus2272.checked2282,CompactPlus2272.small2282,CompactPlus2272.nodes2282,NodePlus35.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus2272.p2283,GridPlus.atNode 2283,GridPlus.atNode 2284,NodePlus35.w43,CompactPlus2272.checked2283,CompactPlus2272.small2283,CompactPlus2272.nodes2283,NodePlus35.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus2272.p2284,GridPlus.atNode 2284,GridPlus.atNode 2285,NodePlus35.w44,CompactPlus2272.checked2284,CompactPlus2272.small2284,CompactPlus2272.nodes2284,NodePlus35.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus2272.p2285,GridPlus.atNode 2285,GridPlus.atNode 2286,NodePlus35.w45,CompactPlus2272.checked2285,CompactPlus2272.small2285,CompactPlus2272.nodes2285,NodePlus35.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus2272.p2286,GridPlus.atNode 2286,GridPlus.atNode 2287,NodePlus35.w46,CompactPlus2272.checked2286,CompactPlus2272.small2286,CompactPlus2272.nodes2286,NodePlus35.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus2272.p2287,GridPlus.atNode 2287,GridPlus.atNode 2288,NodePlus35.w47,CompactPlus2272.checked2287,CompactPlus2272.small2287,CompactPlus2272.nodes2287,NodePlus35.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus2288.p2288,GridPlus.atNode 2288,GridPlus.atNode 2289,NodePlus35.w48,CompactPlus2288.checked2288,CompactPlus2288.small2288,CompactPlus2288.nodes2288,NodePlus35.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus2288.p2289,GridPlus.atNode 2289,GridPlus.atNode 2290,NodePlus35.w49,CompactPlus2288.checked2289,CompactPlus2288.small2289,CompactPlus2288.nodes2289,NodePlus35.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus2288.p2290,GridPlus.atNode 2290,GridPlus.atNode 2291,NodePlus35.w50,CompactPlus2288.checked2290,CompactPlus2288.small2290,CompactPlus2288.nodes2290,NodePlus35.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus2288.p2291,GridPlus.atNode 2291,GridPlus.atNode 2292,NodePlus35.w51,CompactPlus2288.checked2291,CompactPlus2288.small2291,CompactPlus2288.nodes2291,NodePlus35.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus2288.p2292,GridPlus.atNode 2292,GridPlus.atNode 2293,NodePlus35.w52,CompactPlus2288.checked2292,CompactPlus2288.small2292,CompactPlus2288.nodes2292,NodePlus35.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus2288.p2293,GridPlus.atNode 2293,GridPlus.atNode 2294,NodePlus35.w53,CompactPlus2288.checked2293,CompactPlus2288.small2293,CompactPlus2288.nodes2293,NodePlus35.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus2288.p2294,GridPlus.atNode 2294,GridPlus.atNode 2295,NodePlus35.w54,CompactPlus2288.checked2294,CompactPlus2288.small2294,CompactPlus2288.nodes2294,NodePlus35.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus2288.p2295,GridPlus.atNode 2295,GridPlus.atNode 2296,NodePlus35.w55,CompactPlus2288.checked2295,CompactPlus2288.small2295,CompactPlus2288.nodes2295,NodePlus35.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus2288.p2296,GridPlus.atNode 2296,GridPlus.atNode 2297,NodePlus35.w56,CompactPlus2288.checked2296,CompactPlus2288.small2296,CompactPlus2288.nodes2296,NodePlus35.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus2288.p2297,GridPlus.atNode 2297,GridPlus.atNode 2298,NodePlus35.w57,CompactPlus2288.checked2297,CompactPlus2288.small2297,CompactPlus2288.nodes2297,NodePlus35.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus2288.p2298,GridPlus.atNode 2298,GridPlus.atNode 2299,NodePlus35.w58,CompactPlus2288.checked2298,CompactPlus2288.small2298,CompactPlus2288.nodes2298,NodePlus35.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus2288.p2299,GridPlus.atNode 2299,GridPlus.atNode 2300,NodePlus35.w59,CompactPlus2288.checked2299,CompactPlus2288.small2299,CompactPlus2288.nodes2299,NodePlus35.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus2288.p2300,GridPlus.atNode 2300,GridPlus.atNode 2301,NodePlus35.w60,CompactPlus2288.checked2300,CompactPlus2288.small2300,CompactPlus2288.nodes2300,NodePlus35.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus2288.p2301,GridPlus.atNode 2301,GridPlus.atNode 2302,NodePlus35.w61,CompactPlus2288.checked2301,CompactPlus2288.small2301,CompactPlus2288.nodes2301,NodePlus35.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus2288.p2302,GridPlus.atNode 2302,GridPlus.atNode 2303,NodePlus35.w62,CompactPlus2288.checked2302,CompactPlus2288.small2302,CompactPlus2288.nodes2302,NodePlus35.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus2288.p2303,GridPlus.atNode 2303,GridPlus.atNode 2304,NodePlus35.w63,CompactPlus2288.checked2303,CompactPlus2288.small2303,CompactPlus2288.nodes2303,NodePlus35.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (2240+j) ∧
    (atRow j).right=GridPlus.atNode (2240+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus35
