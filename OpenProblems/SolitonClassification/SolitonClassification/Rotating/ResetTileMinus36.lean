import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus2304
import SolitonClassification.Rotating.ResetPackedMinus2320
import SolitonClassification.Rotating.ResetPackedMinus2336
import SolitonClassification.Rotating.ResetPackedMinus2352
namespace SolitonClassification.Rotating.DyadicReset.TileMinus36
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2304.p2304,GridMinus.atNode 2304,GridMinus.atNode 2305,NodeMinus36.w0,CompactMinus2304.checked2304,CompactMinus2304.small2304,CompactMinus2304.nodes2304,NodeMinus36.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2304.p2305,GridMinus.atNode 2305,GridMinus.atNode 2306,NodeMinus36.w1,CompactMinus2304.checked2305,CompactMinus2304.small2305,CompactMinus2304.nodes2305,NodeMinus36.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2304.p2306,GridMinus.atNode 2306,GridMinus.atNode 2307,NodeMinus36.w2,CompactMinus2304.checked2306,CompactMinus2304.small2306,CompactMinus2304.nodes2306,NodeMinus36.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2304.p2307,GridMinus.atNode 2307,GridMinus.atNode 2308,NodeMinus36.w3,CompactMinus2304.checked2307,CompactMinus2304.small2307,CompactMinus2304.nodes2307,NodeMinus36.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2304.p2308,GridMinus.atNode 2308,GridMinus.atNode 2309,NodeMinus36.w4,CompactMinus2304.checked2308,CompactMinus2304.small2308,CompactMinus2304.nodes2308,NodeMinus36.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2304.p2309,GridMinus.atNode 2309,GridMinus.atNode 2310,NodeMinus36.w5,CompactMinus2304.checked2309,CompactMinus2304.small2309,CompactMinus2304.nodes2309,NodeMinus36.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2304.p2310,GridMinus.atNode 2310,GridMinus.atNode 2311,NodeMinus36.w6,CompactMinus2304.checked2310,CompactMinus2304.small2310,CompactMinus2304.nodes2310,NodeMinus36.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2304.p2311,GridMinus.atNode 2311,GridMinus.atNode 2312,NodeMinus36.w7,CompactMinus2304.checked2311,CompactMinus2304.small2311,CompactMinus2304.nodes2311,NodeMinus36.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2304.p2312,GridMinus.atNode 2312,GridMinus.atNode 2313,NodeMinus36.w8,CompactMinus2304.checked2312,CompactMinus2304.small2312,CompactMinus2304.nodes2312,NodeMinus36.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2304.p2313,GridMinus.atNode 2313,GridMinus.atNode 2314,NodeMinus36.w9,CompactMinus2304.checked2313,CompactMinus2304.small2313,CompactMinus2304.nodes2313,NodeMinus36.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2304.p2314,GridMinus.atNode 2314,GridMinus.atNode 2315,NodeMinus36.w10,CompactMinus2304.checked2314,CompactMinus2304.small2314,CompactMinus2304.nodes2314,NodeMinus36.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2304.p2315,GridMinus.atNode 2315,GridMinus.atNode 2316,NodeMinus36.w11,CompactMinus2304.checked2315,CompactMinus2304.small2315,CompactMinus2304.nodes2315,NodeMinus36.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2304.p2316,GridMinus.atNode 2316,GridMinus.atNode 2317,NodeMinus36.w12,CompactMinus2304.checked2316,CompactMinus2304.small2316,CompactMinus2304.nodes2316,NodeMinus36.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2304.p2317,GridMinus.atNode 2317,GridMinus.atNode 2318,NodeMinus36.w13,CompactMinus2304.checked2317,CompactMinus2304.small2317,CompactMinus2304.nodes2317,NodeMinus36.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2304.p2318,GridMinus.atNode 2318,GridMinus.atNode 2319,NodeMinus36.w14,CompactMinus2304.checked2318,CompactMinus2304.small2318,CompactMinus2304.nodes2318,NodeMinus36.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2304.p2319,GridMinus.atNode 2319,GridMinus.atNode 2320,NodeMinus36.w15,CompactMinus2304.checked2319,CompactMinus2304.small2319,CompactMinus2304.nodes2319,NodeMinus36.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2320.p2320,GridMinus.atNode 2320,GridMinus.atNode 2321,NodeMinus36.w16,CompactMinus2320.checked2320,CompactMinus2320.small2320,CompactMinus2320.nodes2320,NodeMinus36.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2320.p2321,GridMinus.atNode 2321,GridMinus.atNode 2322,NodeMinus36.w17,CompactMinus2320.checked2321,CompactMinus2320.small2321,CompactMinus2320.nodes2321,NodeMinus36.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2320.p2322,GridMinus.atNode 2322,GridMinus.atNode 2323,NodeMinus36.w18,CompactMinus2320.checked2322,CompactMinus2320.small2322,CompactMinus2320.nodes2322,NodeMinus36.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2320.p2323,GridMinus.atNode 2323,GridMinus.atNode 2324,NodeMinus36.w19,CompactMinus2320.checked2323,CompactMinus2320.small2323,CompactMinus2320.nodes2323,NodeMinus36.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2320.p2324,GridMinus.atNode 2324,GridMinus.atNode 2325,NodeMinus36.w20,CompactMinus2320.checked2324,CompactMinus2320.small2324,CompactMinus2320.nodes2324,NodeMinus36.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2320.p2325,GridMinus.atNode 2325,GridMinus.atNode 2326,NodeMinus36.w21,CompactMinus2320.checked2325,CompactMinus2320.small2325,CompactMinus2320.nodes2325,NodeMinus36.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2320.p2326,GridMinus.atNode 2326,GridMinus.atNode 2327,NodeMinus36.w22,CompactMinus2320.checked2326,CompactMinus2320.small2326,CompactMinus2320.nodes2326,NodeMinus36.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2320.p2327,GridMinus.atNode 2327,GridMinus.atNode 2328,NodeMinus36.w23,CompactMinus2320.checked2327,CompactMinus2320.small2327,CompactMinus2320.nodes2327,NodeMinus36.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2320.p2328,GridMinus.atNode 2328,GridMinus.atNode 2329,NodeMinus36.w24,CompactMinus2320.checked2328,CompactMinus2320.small2328,CompactMinus2320.nodes2328,NodeMinus36.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2320.p2329,GridMinus.atNode 2329,GridMinus.atNode 2330,NodeMinus36.w25,CompactMinus2320.checked2329,CompactMinus2320.small2329,CompactMinus2320.nodes2329,NodeMinus36.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2320.p2330,GridMinus.atNode 2330,GridMinus.atNode 2331,NodeMinus36.w26,CompactMinus2320.checked2330,CompactMinus2320.small2330,CompactMinus2320.nodes2330,NodeMinus36.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2320.p2331,GridMinus.atNode 2331,GridMinus.atNode 2332,NodeMinus36.w27,CompactMinus2320.checked2331,CompactMinus2320.small2331,CompactMinus2320.nodes2331,NodeMinus36.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2320.p2332,GridMinus.atNode 2332,GridMinus.atNode 2333,NodeMinus36.w28,CompactMinus2320.checked2332,CompactMinus2320.small2332,CompactMinus2320.nodes2332,NodeMinus36.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2320.p2333,GridMinus.atNode 2333,GridMinus.atNode 2334,NodeMinus36.w29,CompactMinus2320.checked2333,CompactMinus2320.small2333,CompactMinus2320.nodes2333,NodeMinus36.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2320.p2334,GridMinus.atNode 2334,GridMinus.atNode 2335,NodeMinus36.w30,CompactMinus2320.checked2334,CompactMinus2320.small2334,CompactMinus2320.nodes2334,NodeMinus36.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2320.p2335,GridMinus.atNode 2335,GridMinus.atNode 2336,NodeMinus36.w31,CompactMinus2320.checked2335,CompactMinus2320.small2335,CompactMinus2320.nodes2335,NodeMinus36.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2336.p2336,GridMinus.atNode 2336,GridMinus.atNode 2337,NodeMinus36.w32,CompactMinus2336.checked2336,CompactMinus2336.small2336,CompactMinus2336.nodes2336,NodeMinus36.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2336.p2337,GridMinus.atNode 2337,GridMinus.atNode 2338,NodeMinus36.w33,CompactMinus2336.checked2337,CompactMinus2336.small2337,CompactMinus2336.nodes2337,NodeMinus36.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2336.p2338,GridMinus.atNode 2338,GridMinus.atNode 2339,NodeMinus36.w34,CompactMinus2336.checked2338,CompactMinus2336.small2338,CompactMinus2336.nodes2338,NodeMinus36.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2336.p2339,GridMinus.atNode 2339,GridMinus.atNode 2340,NodeMinus36.w35,CompactMinus2336.checked2339,CompactMinus2336.small2339,CompactMinus2336.nodes2339,NodeMinus36.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2336.p2340,GridMinus.atNode 2340,GridMinus.atNode 2341,NodeMinus36.w36,CompactMinus2336.checked2340,CompactMinus2336.small2340,CompactMinus2336.nodes2340,NodeMinus36.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2336.p2341,GridMinus.atNode 2341,GridMinus.atNode 2342,NodeMinus36.w37,CompactMinus2336.checked2341,CompactMinus2336.small2341,CompactMinus2336.nodes2341,NodeMinus36.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2336.p2342,GridMinus.atNode 2342,GridMinus.atNode 2343,NodeMinus36.w38,CompactMinus2336.checked2342,CompactMinus2336.small2342,CompactMinus2336.nodes2342,NodeMinus36.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2336.p2343,GridMinus.atNode 2343,GridMinus.atNode 2344,NodeMinus36.w39,CompactMinus2336.checked2343,CompactMinus2336.small2343,CompactMinus2336.nodes2343,NodeMinus36.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2336.p2344,GridMinus.atNode 2344,GridMinus.atNode 2345,NodeMinus36.w40,CompactMinus2336.checked2344,CompactMinus2336.small2344,CompactMinus2336.nodes2344,NodeMinus36.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2336.p2345,GridMinus.atNode 2345,GridMinus.atNode 2346,NodeMinus36.w41,CompactMinus2336.checked2345,CompactMinus2336.small2345,CompactMinus2336.nodes2345,NodeMinus36.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2336.p2346,GridMinus.atNode 2346,GridMinus.atNode 2347,NodeMinus36.w42,CompactMinus2336.checked2346,CompactMinus2336.small2346,CompactMinus2336.nodes2346,NodeMinus36.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2336.p2347,GridMinus.atNode 2347,GridMinus.atNode 2348,NodeMinus36.w43,CompactMinus2336.checked2347,CompactMinus2336.small2347,CompactMinus2336.nodes2347,NodeMinus36.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2336.p2348,GridMinus.atNode 2348,GridMinus.atNode 2349,NodeMinus36.w44,CompactMinus2336.checked2348,CompactMinus2336.small2348,CompactMinus2336.nodes2348,NodeMinus36.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2336.p2349,GridMinus.atNode 2349,GridMinus.atNode 2350,NodeMinus36.w45,CompactMinus2336.checked2349,CompactMinus2336.small2349,CompactMinus2336.nodes2349,NodeMinus36.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2336.p2350,GridMinus.atNode 2350,GridMinus.atNode 2351,NodeMinus36.w46,CompactMinus2336.checked2350,CompactMinus2336.small2350,CompactMinus2336.nodes2350,NodeMinus36.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2336.p2351,GridMinus.atNode 2351,GridMinus.atNode 2352,NodeMinus36.w47,CompactMinus2336.checked2351,CompactMinus2336.small2351,CompactMinus2336.nodes2351,NodeMinus36.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2352.p2352,GridMinus.atNode 2352,GridMinus.atNode 2353,NodeMinus36.w48,CompactMinus2352.checked2352,CompactMinus2352.small2352,CompactMinus2352.nodes2352,NodeMinus36.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2352.p2353,GridMinus.atNode 2353,GridMinus.atNode 2354,NodeMinus36.w49,CompactMinus2352.checked2353,CompactMinus2352.small2353,CompactMinus2352.nodes2353,NodeMinus36.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2352.p2354,GridMinus.atNode 2354,GridMinus.atNode 2355,NodeMinus36.w50,CompactMinus2352.checked2354,CompactMinus2352.small2354,CompactMinus2352.nodes2354,NodeMinus36.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2352.p2355,GridMinus.atNode 2355,GridMinus.atNode 2356,NodeMinus36.w51,CompactMinus2352.checked2355,CompactMinus2352.small2355,CompactMinus2352.nodes2355,NodeMinus36.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2352.p2356,GridMinus.atNode 2356,GridMinus.atNode 2357,NodeMinus36.w52,CompactMinus2352.checked2356,CompactMinus2352.small2356,CompactMinus2352.nodes2356,NodeMinus36.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2352.p2357,GridMinus.atNode 2357,GridMinus.atNode 2358,NodeMinus36.w53,CompactMinus2352.checked2357,CompactMinus2352.small2357,CompactMinus2352.nodes2357,NodeMinus36.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2352.p2358,GridMinus.atNode 2358,GridMinus.atNode 2359,NodeMinus36.w54,CompactMinus2352.checked2358,CompactMinus2352.small2358,CompactMinus2352.nodes2358,NodeMinus36.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2352.p2359,GridMinus.atNode 2359,GridMinus.atNode 2360,NodeMinus36.w55,CompactMinus2352.checked2359,CompactMinus2352.small2359,CompactMinus2352.nodes2359,NodeMinus36.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2352.p2360,GridMinus.atNode 2360,GridMinus.atNode 2361,NodeMinus36.w56,CompactMinus2352.checked2360,CompactMinus2352.small2360,CompactMinus2352.nodes2360,NodeMinus36.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2352.p2361,GridMinus.atNode 2361,GridMinus.atNode 2362,NodeMinus36.w57,CompactMinus2352.checked2361,CompactMinus2352.small2361,CompactMinus2352.nodes2361,NodeMinus36.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2352.p2362,GridMinus.atNode 2362,GridMinus.atNode 2363,NodeMinus36.w58,CompactMinus2352.checked2362,CompactMinus2352.small2362,CompactMinus2352.nodes2362,NodeMinus36.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2352.p2363,GridMinus.atNode 2363,GridMinus.atNode 2364,NodeMinus36.w59,CompactMinus2352.checked2363,CompactMinus2352.small2363,CompactMinus2352.nodes2363,NodeMinus36.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2352.p2364,GridMinus.atNode 2364,GridMinus.atNode 2365,NodeMinus36.w60,CompactMinus2352.checked2364,CompactMinus2352.small2364,CompactMinus2352.nodes2364,NodeMinus36.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2352.p2365,GridMinus.atNode 2365,GridMinus.atNode 2366,NodeMinus36.w61,CompactMinus2352.checked2365,CompactMinus2352.small2365,CompactMinus2352.nodes2365,NodeMinus36.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2352.p2366,GridMinus.atNode 2366,GridMinus.atNode 2367,NodeMinus36.w62,CompactMinus2352.checked2366,CompactMinus2352.small2366,CompactMinus2352.nodes2366,NodeMinus36.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2352.p2367,GridMinus.atNode 2367,GridMinus.atNode 2368,NodeMinus36.w63,CompactMinus2352.checked2367,CompactMinus2352.small2367,CompactMinus2352.nodes2367,NodeMinus36.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (2304+j) ∧
    (atRow j).right=GridMinus.atNode (2304+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus36
