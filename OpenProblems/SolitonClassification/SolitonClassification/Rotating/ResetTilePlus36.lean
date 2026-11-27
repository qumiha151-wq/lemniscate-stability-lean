import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus2304
import SolitonClassification.Rotating.ResetPackedPlus2320
import SolitonClassification.Rotating.ResetPackedPlus2336
import SolitonClassification.Rotating.ResetPackedPlus2352
namespace SolitonClassification.Rotating.DyadicReset.TilePlus36
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus2304.p2304,GridPlus.atNode 2304,GridPlus.atNode 2305,NodePlus36.w0,CompactPlus2304.checked2304,CompactPlus2304.small2304,CompactPlus2304.nodes2304,NodePlus36.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus2304.p2305,GridPlus.atNode 2305,GridPlus.atNode 2306,NodePlus36.w1,CompactPlus2304.checked2305,CompactPlus2304.small2305,CompactPlus2304.nodes2305,NodePlus36.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus2304.p2306,GridPlus.atNode 2306,GridPlus.atNode 2307,NodePlus36.w2,CompactPlus2304.checked2306,CompactPlus2304.small2306,CompactPlus2304.nodes2306,NodePlus36.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus2304.p2307,GridPlus.atNode 2307,GridPlus.atNode 2308,NodePlus36.w3,CompactPlus2304.checked2307,CompactPlus2304.small2307,CompactPlus2304.nodes2307,NodePlus36.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus2304.p2308,GridPlus.atNode 2308,GridPlus.atNode 2309,NodePlus36.w4,CompactPlus2304.checked2308,CompactPlus2304.small2308,CompactPlus2304.nodes2308,NodePlus36.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus2304.p2309,GridPlus.atNode 2309,GridPlus.atNode 2310,NodePlus36.w5,CompactPlus2304.checked2309,CompactPlus2304.small2309,CompactPlus2304.nodes2309,NodePlus36.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus2304.p2310,GridPlus.atNode 2310,GridPlus.atNode 2311,NodePlus36.w6,CompactPlus2304.checked2310,CompactPlus2304.small2310,CompactPlus2304.nodes2310,NodePlus36.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus2304.p2311,GridPlus.atNode 2311,GridPlus.atNode 2312,NodePlus36.w7,CompactPlus2304.checked2311,CompactPlus2304.small2311,CompactPlus2304.nodes2311,NodePlus36.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus2304.p2312,GridPlus.atNode 2312,GridPlus.atNode 2313,NodePlus36.w8,CompactPlus2304.checked2312,CompactPlus2304.small2312,CompactPlus2304.nodes2312,NodePlus36.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus2304.p2313,GridPlus.atNode 2313,GridPlus.atNode 2314,NodePlus36.w9,CompactPlus2304.checked2313,CompactPlus2304.small2313,CompactPlus2304.nodes2313,NodePlus36.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus2304.p2314,GridPlus.atNode 2314,GridPlus.atNode 2315,NodePlus36.w10,CompactPlus2304.checked2314,CompactPlus2304.small2314,CompactPlus2304.nodes2314,NodePlus36.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus2304.p2315,GridPlus.atNode 2315,GridPlus.atNode 2316,NodePlus36.w11,CompactPlus2304.checked2315,CompactPlus2304.small2315,CompactPlus2304.nodes2315,NodePlus36.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus2304.p2316,GridPlus.atNode 2316,GridPlus.atNode 2317,NodePlus36.w12,CompactPlus2304.checked2316,CompactPlus2304.small2316,CompactPlus2304.nodes2316,NodePlus36.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus2304.p2317,GridPlus.atNode 2317,GridPlus.atNode 2318,NodePlus36.w13,CompactPlus2304.checked2317,CompactPlus2304.small2317,CompactPlus2304.nodes2317,NodePlus36.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus2304.p2318,GridPlus.atNode 2318,GridPlus.atNode 2319,NodePlus36.w14,CompactPlus2304.checked2318,CompactPlus2304.small2318,CompactPlus2304.nodes2318,NodePlus36.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus2304.p2319,GridPlus.atNode 2319,GridPlus.atNode 2320,NodePlus36.w15,CompactPlus2304.checked2319,CompactPlus2304.small2319,CompactPlus2304.nodes2319,NodePlus36.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus2320.p2320,GridPlus.atNode 2320,GridPlus.atNode 2321,NodePlus36.w16,CompactPlus2320.checked2320,CompactPlus2320.small2320,CompactPlus2320.nodes2320,NodePlus36.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus2320.p2321,GridPlus.atNode 2321,GridPlus.atNode 2322,NodePlus36.w17,CompactPlus2320.checked2321,CompactPlus2320.small2321,CompactPlus2320.nodes2321,NodePlus36.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus2320.p2322,GridPlus.atNode 2322,GridPlus.atNode 2323,NodePlus36.w18,CompactPlus2320.checked2322,CompactPlus2320.small2322,CompactPlus2320.nodes2322,NodePlus36.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus2320.p2323,GridPlus.atNode 2323,GridPlus.atNode 2324,NodePlus36.w19,CompactPlus2320.checked2323,CompactPlus2320.small2323,CompactPlus2320.nodes2323,NodePlus36.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus2320.p2324,GridPlus.atNode 2324,GridPlus.atNode 2325,NodePlus36.w20,CompactPlus2320.checked2324,CompactPlus2320.small2324,CompactPlus2320.nodes2324,NodePlus36.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus2320.p2325,GridPlus.atNode 2325,GridPlus.atNode 2326,NodePlus36.w21,CompactPlus2320.checked2325,CompactPlus2320.small2325,CompactPlus2320.nodes2325,NodePlus36.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus2320.p2326,GridPlus.atNode 2326,GridPlus.atNode 2327,NodePlus36.w22,CompactPlus2320.checked2326,CompactPlus2320.small2326,CompactPlus2320.nodes2326,NodePlus36.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus2320.p2327,GridPlus.atNode 2327,GridPlus.atNode 2328,NodePlus36.w23,CompactPlus2320.checked2327,CompactPlus2320.small2327,CompactPlus2320.nodes2327,NodePlus36.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus2320.p2328,GridPlus.atNode 2328,GridPlus.atNode 2329,NodePlus36.w24,CompactPlus2320.checked2328,CompactPlus2320.small2328,CompactPlus2320.nodes2328,NodePlus36.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus2320.p2329,GridPlus.atNode 2329,GridPlus.atNode 2330,NodePlus36.w25,CompactPlus2320.checked2329,CompactPlus2320.small2329,CompactPlus2320.nodes2329,NodePlus36.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus2320.p2330,GridPlus.atNode 2330,GridPlus.atNode 2331,NodePlus36.w26,CompactPlus2320.checked2330,CompactPlus2320.small2330,CompactPlus2320.nodes2330,NodePlus36.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus2320.p2331,GridPlus.atNode 2331,GridPlus.atNode 2332,NodePlus36.w27,CompactPlus2320.checked2331,CompactPlus2320.small2331,CompactPlus2320.nodes2331,NodePlus36.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus2320.p2332,GridPlus.atNode 2332,GridPlus.atNode 2333,NodePlus36.w28,CompactPlus2320.checked2332,CompactPlus2320.small2332,CompactPlus2320.nodes2332,NodePlus36.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus2320.p2333,GridPlus.atNode 2333,GridPlus.atNode 2334,NodePlus36.w29,CompactPlus2320.checked2333,CompactPlus2320.small2333,CompactPlus2320.nodes2333,NodePlus36.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus2320.p2334,GridPlus.atNode 2334,GridPlus.atNode 2335,NodePlus36.w30,CompactPlus2320.checked2334,CompactPlus2320.small2334,CompactPlus2320.nodes2334,NodePlus36.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus2320.p2335,GridPlus.atNode 2335,GridPlus.atNode 2336,NodePlus36.w31,CompactPlus2320.checked2335,CompactPlus2320.small2335,CompactPlus2320.nodes2335,NodePlus36.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus2336.p2336,GridPlus.atNode 2336,GridPlus.atNode 2337,NodePlus36.w32,CompactPlus2336.checked2336,CompactPlus2336.small2336,CompactPlus2336.nodes2336,NodePlus36.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus2336.p2337,GridPlus.atNode 2337,GridPlus.atNode 2338,NodePlus36.w33,CompactPlus2336.checked2337,CompactPlus2336.small2337,CompactPlus2336.nodes2337,NodePlus36.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus2336.p2338,GridPlus.atNode 2338,GridPlus.atNode 2339,NodePlus36.w34,CompactPlus2336.checked2338,CompactPlus2336.small2338,CompactPlus2336.nodes2338,NodePlus36.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus2336.p2339,GridPlus.atNode 2339,GridPlus.atNode 2340,NodePlus36.w35,CompactPlus2336.checked2339,CompactPlus2336.small2339,CompactPlus2336.nodes2339,NodePlus36.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus2336.p2340,GridPlus.atNode 2340,GridPlus.atNode 2341,NodePlus36.w36,CompactPlus2336.checked2340,CompactPlus2336.small2340,CompactPlus2336.nodes2340,NodePlus36.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus2336.p2341,GridPlus.atNode 2341,GridPlus.atNode 2342,NodePlus36.w37,CompactPlus2336.checked2341,CompactPlus2336.small2341,CompactPlus2336.nodes2341,NodePlus36.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus2336.p2342,GridPlus.atNode 2342,GridPlus.atNode 2343,NodePlus36.w38,CompactPlus2336.checked2342,CompactPlus2336.small2342,CompactPlus2336.nodes2342,NodePlus36.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus2336.p2343,GridPlus.atNode 2343,GridPlus.atNode 2344,NodePlus36.w39,CompactPlus2336.checked2343,CompactPlus2336.small2343,CompactPlus2336.nodes2343,NodePlus36.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus2336.p2344,GridPlus.atNode 2344,GridPlus.atNode 2345,NodePlus36.w40,CompactPlus2336.checked2344,CompactPlus2336.small2344,CompactPlus2336.nodes2344,NodePlus36.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus2336.p2345,GridPlus.atNode 2345,GridPlus.atNode 2346,NodePlus36.w41,CompactPlus2336.checked2345,CompactPlus2336.small2345,CompactPlus2336.nodes2345,NodePlus36.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus2336.p2346,GridPlus.atNode 2346,GridPlus.atNode 2347,NodePlus36.w42,CompactPlus2336.checked2346,CompactPlus2336.small2346,CompactPlus2336.nodes2346,NodePlus36.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus2336.p2347,GridPlus.atNode 2347,GridPlus.atNode 2348,NodePlus36.w43,CompactPlus2336.checked2347,CompactPlus2336.small2347,CompactPlus2336.nodes2347,NodePlus36.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus2336.p2348,GridPlus.atNode 2348,GridPlus.atNode 2349,NodePlus36.w44,CompactPlus2336.checked2348,CompactPlus2336.small2348,CompactPlus2336.nodes2348,NodePlus36.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus2336.p2349,GridPlus.atNode 2349,GridPlus.atNode 2350,NodePlus36.w45,CompactPlus2336.checked2349,CompactPlus2336.small2349,CompactPlus2336.nodes2349,NodePlus36.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus2336.p2350,GridPlus.atNode 2350,GridPlus.atNode 2351,NodePlus36.w46,CompactPlus2336.checked2350,CompactPlus2336.small2350,CompactPlus2336.nodes2350,NodePlus36.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus2336.p2351,GridPlus.atNode 2351,GridPlus.atNode 2352,NodePlus36.w47,CompactPlus2336.checked2351,CompactPlus2336.small2351,CompactPlus2336.nodes2351,NodePlus36.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus2352.p2352,GridPlus.atNode 2352,GridPlus.atNode 2353,NodePlus36.w48,CompactPlus2352.checked2352,CompactPlus2352.small2352,CompactPlus2352.nodes2352,NodePlus36.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus2352.p2353,GridPlus.atNode 2353,GridPlus.atNode 2354,NodePlus36.w49,CompactPlus2352.checked2353,CompactPlus2352.small2353,CompactPlus2352.nodes2353,NodePlus36.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus2352.p2354,GridPlus.atNode 2354,GridPlus.atNode 2355,NodePlus36.w50,CompactPlus2352.checked2354,CompactPlus2352.small2354,CompactPlus2352.nodes2354,NodePlus36.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus2352.p2355,GridPlus.atNode 2355,GridPlus.atNode 2356,NodePlus36.w51,CompactPlus2352.checked2355,CompactPlus2352.small2355,CompactPlus2352.nodes2355,NodePlus36.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus2352.p2356,GridPlus.atNode 2356,GridPlus.atNode 2357,NodePlus36.w52,CompactPlus2352.checked2356,CompactPlus2352.small2356,CompactPlus2352.nodes2356,NodePlus36.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus2352.p2357,GridPlus.atNode 2357,GridPlus.atNode 2358,NodePlus36.w53,CompactPlus2352.checked2357,CompactPlus2352.small2357,CompactPlus2352.nodes2357,NodePlus36.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus2352.p2358,GridPlus.atNode 2358,GridPlus.atNode 2359,NodePlus36.w54,CompactPlus2352.checked2358,CompactPlus2352.small2358,CompactPlus2352.nodes2358,NodePlus36.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus2352.p2359,GridPlus.atNode 2359,GridPlus.atNode 2360,NodePlus36.w55,CompactPlus2352.checked2359,CompactPlus2352.small2359,CompactPlus2352.nodes2359,NodePlus36.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus2352.p2360,GridPlus.atNode 2360,GridPlus.atNode 2361,NodePlus36.w56,CompactPlus2352.checked2360,CompactPlus2352.small2360,CompactPlus2352.nodes2360,NodePlus36.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus2352.p2361,GridPlus.atNode 2361,GridPlus.atNode 2362,NodePlus36.w57,CompactPlus2352.checked2361,CompactPlus2352.small2361,CompactPlus2352.nodes2361,NodePlus36.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus2352.p2362,GridPlus.atNode 2362,GridPlus.atNode 2363,NodePlus36.w58,CompactPlus2352.checked2362,CompactPlus2352.small2362,CompactPlus2352.nodes2362,NodePlus36.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus2352.p2363,GridPlus.atNode 2363,GridPlus.atNode 2364,NodePlus36.w59,CompactPlus2352.checked2363,CompactPlus2352.small2363,CompactPlus2352.nodes2363,NodePlus36.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus2352.p2364,GridPlus.atNode 2364,GridPlus.atNode 2365,NodePlus36.w60,CompactPlus2352.checked2364,CompactPlus2352.small2364,CompactPlus2352.nodes2364,NodePlus36.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus2352.p2365,GridPlus.atNode 2365,GridPlus.atNode 2366,NodePlus36.w61,CompactPlus2352.checked2365,CompactPlus2352.small2365,CompactPlus2352.nodes2365,NodePlus36.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus2352.p2366,GridPlus.atNode 2366,GridPlus.atNode 2367,NodePlus36.w62,CompactPlus2352.checked2366,CompactPlus2352.small2366,CompactPlus2352.nodes2366,NodePlus36.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus2352.p2367,GridPlus.atNode 2367,GridPlus.atNode 2368,NodePlus36.w63,CompactPlus2352.checked2367,CompactPlus2352.small2367,CompactPlus2352.nodes2367,NodePlus36.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (2304+j) ∧
    (atRow j).right=GridPlus.atNode (2304+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus36
