import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus2368
import SolitonClassification.Rotating.ResetPackedMinus2384
import SolitonClassification.Rotating.ResetPackedMinus2400
import SolitonClassification.Rotating.ResetPackedMinus2416
namespace SolitonClassification.Rotating.DyadicReset.TileMinus37
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2368.p2368,GridMinus.atNode 2368,GridMinus.atNode 2369,NodeMinus37.w0,CompactMinus2368.checked2368,CompactMinus2368.small2368,CompactMinus2368.nodes2368,NodeMinus37.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2368.p2369,GridMinus.atNode 2369,GridMinus.atNode 2370,NodeMinus37.w1,CompactMinus2368.checked2369,CompactMinus2368.small2369,CompactMinus2368.nodes2369,NodeMinus37.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2368.p2370,GridMinus.atNode 2370,GridMinus.atNode 2371,NodeMinus37.w2,CompactMinus2368.checked2370,CompactMinus2368.small2370,CompactMinus2368.nodes2370,NodeMinus37.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2368.p2371,GridMinus.atNode 2371,GridMinus.atNode 2372,NodeMinus37.w3,CompactMinus2368.checked2371,CompactMinus2368.small2371,CompactMinus2368.nodes2371,NodeMinus37.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2368.p2372,GridMinus.atNode 2372,GridMinus.atNode 2373,NodeMinus37.w4,CompactMinus2368.checked2372,CompactMinus2368.small2372,CompactMinus2368.nodes2372,NodeMinus37.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2368.p2373,GridMinus.atNode 2373,GridMinus.atNode 2374,NodeMinus37.w5,CompactMinus2368.checked2373,CompactMinus2368.small2373,CompactMinus2368.nodes2373,NodeMinus37.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2368.p2374,GridMinus.atNode 2374,GridMinus.atNode 2375,NodeMinus37.w6,CompactMinus2368.checked2374,CompactMinus2368.small2374,CompactMinus2368.nodes2374,NodeMinus37.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2368.p2375,GridMinus.atNode 2375,GridMinus.atNode 2376,NodeMinus37.w7,CompactMinus2368.checked2375,CompactMinus2368.small2375,CompactMinus2368.nodes2375,NodeMinus37.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2368.p2376,GridMinus.atNode 2376,GridMinus.atNode 2377,NodeMinus37.w8,CompactMinus2368.checked2376,CompactMinus2368.small2376,CompactMinus2368.nodes2376,NodeMinus37.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2368.p2377,GridMinus.atNode 2377,GridMinus.atNode 2378,NodeMinus37.w9,CompactMinus2368.checked2377,CompactMinus2368.small2377,CompactMinus2368.nodes2377,NodeMinus37.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2368.p2378,GridMinus.atNode 2378,GridMinus.atNode 2379,NodeMinus37.w10,CompactMinus2368.checked2378,CompactMinus2368.small2378,CompactMinus2368.nodes2378,NodeMinus37.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2368.p2379,GridMinus.atNode 2379,GridMinus.atNode 2380,NodeMinus37.w11,CompactMinus2368.checked2379,CompactMinus2368.small2379,CompactMinus2368.nodes2379,NodeMinus37.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2368.p2380,GridMinus.atNode 2380,GridMinus.atNode 2381,NodeMinus37.w12,CompactMinus2368.checked2380,CompactMinus2368.small2380,CompactMinus2368.nodes2380,NodeMinus37.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2368.p2381,GridMinus.atNode 2381,GridMinus.atNode 2382,NodeMinus37.w13,CompactMinus2368.checked2381,CompactMinus2368.small2381,CompactMinus2368.nodes2381,NodeMinus37.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2368.p2382,GridMinus.atNode 2382,GridMinus.atNode 2383,NodeMinus37.w14,CompactMinus2368.checked2382,CompactMinus2368.small2382,CompactMinus2368.nodes2382,NodeMinus37.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2368.p2383,GridMinus.atNode 2383,GridMinus.atNode 2384,NodeMinus37.w15,CompactMinus2368.checked2383,CompactMinus2368.small2383,CompactMinus2368.nodes2383,NodeMinus37.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2384.p2384,GridMinus.atNode 2384,GridMinus.atNode 2385,NodeMinus37.w16,CompactMinus2384.checked2384,CompactMinus2384.small2384,CompactMinus2384.nodes2384,NodeMinus37.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2384.p2385,GridMinus.atNode 2385,GridMinus.atNode 2386,NodeMinus37.w17,CompactMinus2384.checked2385,CompactMinus2384.small2385,CompactMinus2384.nodes2385,NodeMinus37.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2384.p2386,GridMinus.atNode 2386,GridMinus.atNode 2387,NodeMinus37.w18,CompactMinus2384.checked2386,CompactMinus2384.small2386,CompactMinus2384.nodes2386,NodeMinus37.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2384.p2387,GridMinus.atNode 2387,GridMinus.atNode 2388,NodeMinus37.w19,CompactMinus2384.checked2387,CompactMinus2384.small2387,CompactMinus2384.nodes2387,NodeMinus37.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2384.p2388,GridMinus.atNode 2388,GridMinus.atNode 2389,NodeMinus37.w20,CompactMinus2384.checked2388,CompactMinus2384.small2388,CompactMinus2384.nodes2388,NodeMinus37.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2384.p2389,GridMinus.atNode 2389,GridMinus.atNode 2390,NodeMinus37.w21,CompactMinus2384.checked2389,CompactMinus2384.small2389,CompactMinus2384.nodes2389,NodeMinus37.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2384.p2390,GridMinus.atNode 2390,GridMinus.atNode 2391,NodeMinus37.w22,CompactMinus2384.checked2390,CompactMinus2384.small2390,CompactMinus2384.nodes2390,NodeMinus37.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2384.p2391,GridMinus.atNode 2391,GridMinus.atNode 2392,NodeMinus37.w23,CompactMinus2384.checked2391,CompactMinus2384.small2391,CompactMinus2384.nodes2391,NodeMinus37.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2384.p2392,GridMinus.atNode 2392,GridMinus.atNode 2393,NodeMinus37.w24,CompactMinus2384.checked2392,CompactMinus2384.small2392,CompactMinus2384.nodes2392,NodeMinus37.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2384.p2393,GridMinus.atNode 2393,GridMinus.atNode 2394,NodeMinus37.w25,CompactMinus2384.checked2393,CompactMinus2384.small2393,CompactMinus2384.nodes2393,NodeMinus37.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2384.p2394,GridMinus.atNode 2394,GridMinus.atNode 2395,NodeMinus37.w26,CompactMinus2384.checked2394,CompactMinus2384.small2394,CompactMinus2384.nodes2394,NodeMinus37.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2384.p2395,GridMinus.atNode 2395,GridMinus.atNode 2396,NodeMinus37.w27,CompactMinus2384.checked2395,CompactMinus2384.small2395,CompactMinus2384.nodes2395,NodeMinus37.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2384.p2396,GridMinus.atNode 2396,GridMinus.atNode 2397,NodeMinus37.w28,CompactMinus2384.checked2396,CompactMinus2384.small2396,CompactMinus2384.nodes2396,NodeMinus37.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2384.p2397,GridMinus.atNode 2397,GridMinus.atNode 2398,NodeMinus37.w29,CompactMinus2384.checked2397,CompactMinus2384.small2397,CompactMinus2384.nodes2397,NodeMinus37.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2384.p2398,GridMinus.atNode 2398,GridMinus.atNode 2399,NodeMinus37.w30,CompactMinus2384.checked2398,CompactMinus2384.small2398,CompactMinus2384.nodes2398,NodeMinus37.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2384.p2399,GridMinus.atNode 2399,GridMinus.atNode 2400,NodeMinus37.w31,CompactMinus2384.checked2399,CompactMinus2384.small2399,CompactMinus2384.nodes2399,NodeMinus37.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2400.p2400,GridMinus.atNode 2400,GridMinus.atNode 2401,NodeMinus37.w32,CompactMinus2400.checked2400,CompactMinus2400.small2400,CompactMinus2400.nodes2400,NodeMinus37.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2400.p2401,GridMinus.atNode 2401,GridMinus.atNode 2402,NodeMinus37.w33,CompactMinus2400.checked2401,CompactMinus2400.small2401,CompactMinus2400.nodes2401,NodeMinus37.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2400.p2402,GridMinus.atNode 2402,GridMinus.atNode 2403,NodeMinus37.w34,CompactMinus2400.checked2402,CompactMinus2400.small2402,CompactMinus2400.nodes2402,NodeMinus37.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2400.p2403,GridMinus.atNode 2403,GridMinus.atNode 2404,NodeMinus37.w35,CompactMinus2400.checked2403,CompactMinus2400.small2403,CompactMinus2400.nodes2403,NodeMinus37.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2400.p2404,GridMinus.atNode 2404,GridMinus.atNode 2405,NodeMinus37.w36,CompactMinus2400.checked2404,CompactMinus2400.small2404,CompactMinus2400.nodes2404,NodeMinus37.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2400.p2405,GridMinus.atNode 2405,GridMinus.atNode 2406,NodeMinus37.w37,CompactMinus2400.checked2405,CompactMinus2400.small2405,CompactMinus2400.nodes2405,NodeMinus37.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2400.p2406,GridMinus.atNode 2406,GridMinus.atNode 2407,NodeMinus37.w38,CompactMinus2400.checked2406,CompactMinus2400.small2406,CompactMinus2400.nodes2406,NodeMinus37.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2400.p2407,GridMinus.atNode 2407,GridMinus.atNode 2408,NodeMinus37.w39,CompactMinus2400.checked2407,CompactMinus2400.small2407,CompactMinus2400.nodes2407,NodeMinus37.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2400.p2408,GridMinus.atNode 2408,GridMinus.atNode 2409,NodeMinus37.w40,CompactMinus2400.checked2408,CompactMinus2400.small2408,CompactMinus2400.nodes2408,NodeMinus37.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2400.p2409,GridMinus.atNode 2409,GridMinus.atNode 2410,NodeMinus37.w41,CompactMinus2400.checked2409,CompactMinus2400.small2409,CompactMinus2400.nodes2409,NodeMinus37.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2400.p2410,GridMinus.atNode 2410,GridMinus.atNode 2411,NodeMinus37.w42,CompactMinus2400.checked2410,CompactMinus2400.small2410,CompactMinus2400.nodes2410,NodeMinus37.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2400.p2411,GridMinus.atNode 2411,GridMinus.atNode 2412,NodeMinus37.w43,CompactMinus2400.checked2411,CompactMinus2400.small2411,CompactMinus2400.nodes2411,NodeMinus37.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2400.p2412,GridMinus.atNode 2412,GridMinus.atNode 2413,NodeMinus37.w44,CompactMinus2400.checked2412,CompactMinus2400.small2412,CompactMinus2400.nodes2412,NodeMinus37.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2400.p2413,GridMinus.atNode 2413,GridMinus.atNode 2414,NodeMinus37.w45,CompactMinus2400.checked2413,CompactMinus2400.small2413,CompactMinus2400.nodes2413,NodeMinus37.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2400.p2414,GridMinus.atNode 2414,GridMinus.atNode 2415,NodeMinus37.w46,CompactMinus2400.checked2414,CompactMinus2400.small2414,CompactMinus2400.nodes2414,NodeMinus37.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2400.p2415,GridMinus.atNode 2415,GridMinus.atNode 2416,NodeMinus37.w47,CompactMinus2400.checked2415,CompactMinus2400.small2415,CompactMinus2400.nodes2415,NodeMinus37.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2416.p2416,GridMinus.atNode 2416,GridMinus.atNode 2417,NodeMinus37.w48,CompactMinus2416.checked2416,CompactMinus2416.small2416,CompactMinus2416.nodes2416,NodeMinus37.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2416.p2417,GridMinus.atNode 2417,GridMinus.atNode 2418,NodeMinus37.w49,CompactMinus2416.checked2417,CompactMinus2416.small2417,CompactMinus2416.nodes2417,NodeMinus37.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2416.p2418,GridMinus.atNode 2418,GridMinus.atNode 2419,NodeMinus37.w50,CompactMinus2416.checked2418,CompactMinus2416.small2418,CompactMinus2416.nodes2418,NodeMinus37.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2416.p2419,GridMinus.atNode 2419,GridMinus.atNode 2420,NodeMinus37.w51,CompactMinus2416.checked2419,CompactMinus2416.small2419,CompactMinus2416.nodes2419,NodeMinus37.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2416.p2420,GridMinus.atNode 2420,GridMinus.atNode 2421,NodeMinus37.w52,CompactMinus2416.checked2420,CompactMinus2416.small2420,CompactMinus2416.nodes2420,NodeMinus37.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2416.p2421,GridMinus.atNode 2421,GridMinus.atNode 2422,NodeMinus37.w53,CompactMinus2416.checked2421,CompactMinus2416.small2421,CompactMinus2416.nodes2421,NodeMinus37.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2416.p2422,GridMinus.atNode 2422,GridMinus.atNode 2423,NodeMinus37.w54,CompactMinus2416.checked2422,CompactMinus2416.small2422,CompactMinus2416.nodes2422,NodeMinus37.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2416.p2423,GridMinus.atNode 2423,GridMinus.atNode 2424,NodeMinus37.w55,CompactMinus2416.checked2423,CompactMinus2416.small2423,CompactMinus2416.nodes2423,NodeMinus37.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2416.p2424,GridMinus.atNode 2424,GridMinus.atNode 2425,NodeMinus37.w56,CompactMinus2416.checked2424,CompactMinus2416.small2424,CompactMinus2416.nodes2424,NodeMinus37.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2416.p2425,GridMinus.atNode 2425,GridMinus.atNode 2426,NodeMinus37.w57,CompactMinus2416.checked2425,CompactMinus2416.small2425,CompactMinus2416.nodes2425,NodeMinus37.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2416.p2426,GridMinus.atNode 2426,GridMinus.atNode 2427,NodeMinus37.w58,CompactMinus2416.checked2426,CompactMinus2416.small2426,CompactMinus2416.nodes2426,NodeMinus37.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2416.p2427,GridMinus.atNode 2427,GridMinus.atNode 2428,NodeMinus37.w59,CompactMinus2416.checked2427,CompactMinus2416.small2427,CompactMinus2416.nodes2427,NodeMinus37.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2416.p2428,GridMinus.atNode 2428,GridMinus.atNode 2429,NodeMinus37.w60,CompactMinus2416.checked2428,CompactMinus2416.small2428,CompactMinus2416.nodes2428,NodeMinus37.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2416.p2429,GridMinus.atNode 2429,GridMinus.atNode 2430,NodeMinus37.w61,CompactMinus2416.checked2429,CompactMinus2416.small2429,CompactMinus2416.nodes2429,NodeMinus37.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2416.p2430,GridMinus.atNode 2430,GridMinus.atNode 2431,NodeMinus37.w62,CompactMinus2416.checked2430,CompactMinus2416.small2430,CompactMinus2416.nodes2430,NodeMinus37.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2416.p2431,GridMinus.atNode 2431,GridMinus.atNode 2432,NodeMinus37.w63,CompactMinus2416.checked2431,CompactMinus2416.small2431,CompactMinus2416.nodes2431,NodeMinus37.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (2368+j) ∧
    (atRow j).right=GridMinus.atNode (2368+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus37
