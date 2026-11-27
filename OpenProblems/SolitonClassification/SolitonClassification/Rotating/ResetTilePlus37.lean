import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus2368
import SolitonClassification.Rotating.ResetPackedPlus2384
import SolitonClassification.Rotating.ResetPackedPlus2400
import SolitonClassification.Rotating.ResetPackedPlus2416
namespace SolitonClassification.Rotating.DyadicReset.TilePlus37
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus2368.p2368,GridPlus.atNode 2368,GridPlus.atNode 2369,NodePlus37.w0,CompactPlus2368.checked2368,CompactPlus2368.small2368,CompactPlus2368.nodes2368,NodePlus37.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus2368.p2369,GridPlus.atNode 2369,GridPlus.atNode 2370,NodePlus37.w1,CompactPlus2368.checked2369,CompactPlus2368.small2369,CompactPlus2368.nodes2369,NodePlus37.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus2368.p2370,GridPlus.atNode 2370,GridPlus.atNode 2371,NodePlus37.w2,CompactPlus2368.checked2370,CompactPlus2368.small2370,CompactPlus2368.nodes2370,NodePlus37.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus2368.p2371,GridPlus.atNode 2371,GridPlus.atNode 2372,NodePlus37.w3,CompactPlus2368.checked2371,CompactPlus2368.small2371,CompactPlus2368.nodes2371,NodePlus37.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus2368.p2372,GridPlus.atNode 2372,GridPlus.atNode 2373,NodePlus37.w4,CompactPlus2368.checked2372,CompactPlus2368.small2372,CompactPlus2368.nodes2372,NodePlus37.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus2368.p2373,GridPlus.atNode 2373,GridPlus.atNode 2374,NodePlus37.w5,CompactPlus2368.checked2373,CompactPlus2368.small2373,CompactPlus2368.nodes2373,NodePlus37.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus2368.p2374,GridPlus.atNode 2374,GridPlus.atNode 2375,NodePlus37.w6,CompactPlus2368.checked2374,CompactPlus2368.small2374,CompactPlus2368.nodes2374,NodePlus37.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus2368.p2375,GridPlus.atNode 2375,GridPlus.atNode 2376,NodePlus37.w7,CompactPlus2368.checked2375,CompactPlus2368.small2375,CompactPlus2368.nodes2375,NodePlus37.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus2368.p2376,GridPlus.atNode 2376,GridPlus.atNode 2377,NodePlus37.w8,CompactPlus2368.checked2376,CompactPlus2368.small2376,CompactPlus2368.nodes2376,NodePlus37.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus2368.p2377,GridPlus.atNode 2377,GridPlus.atNode 2378,NodePlus37.w9,CompactPlus2368.checked2377,CompactPlus2368.small2377,CompactPlus2368.nodes2377,NodePlus37.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus2368.p2378,GridPlus.atNode 2378,GridPlus.atNode 2379,NodePlus37.w10,CompactPlus2368.checked2378,CompactPlus2368.small2378,CompactPlus2368.nodes2378,NodePlus37.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus2368.p2379,GridPlus.atNode 2379,GridPlus.atNode 2380,NodePlus37.w11,CompactPlus2368.checked2379,CompactPlus2368.small2379,CompactPlus2368.nodes2379,NodePlus37.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus2368.p2380,GridPlus.atNode 2380,GridPlus.atNode 2381,NodePlus37.w12,CompactPlus2368.checked2380,CompactPlus2368.small2380,CompactPlus2368.nodes2380,NodePlus37.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus2368.p2381,GridPlus.atNode 2381,GridPlus.atNode 2382,NodePlus37.w13,CompactPlus2368.checked2381,CompactPlus2368.small2381,CompactPlus2368.nodes2381,NodePlus37.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus2368.p2382,GridPlus.atNode 2382,GridPlus.atNode 2383,NodePlus37.w14,CompactPlus2368.checked2382,CompactPlus2368.small2382,CompactPlus2368.nodes2382,NodePlus37.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus2368.p2383,GridPlus.atNode 2383,GridPlus.atNode 2384,NodePlus37.w15,CompactPlus2368.checked2383,CompactPlus2368.small2383,CompactPlus2368.nodes2383,NodePlus37.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus2384.p2384,GridPlus.atNode 2384,GridPlus.atNode 2385,NodePlus37.w16,CompactPlus2384.checked2384,CompactPlus2384.small2384,CompactPlus2384.nodes2384,NodePlus37.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus2384.p2385,GridPlus.atNode 2385,GridPlus.atNode 2386,NodePlus37.w17,CompactPlus2384.checked2385,CompactPlus2384.small2385,CompactPlus2384.nodes2385,NodePlus37.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus2384.p2386,GridPlus.atNode 2386,GridPlus.atNode 2387,NodePlus37.w18,CompactPlus2384.checked2386,CompactPlus2384.small2386,CompactPlus2384.nodes2386,NodePlus37.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus2384.p2387,GridPlus.atNode 2387,GridPlus.atNode 2388,NodePlus37.w19,CompactPlus2384.checked2387,CompactPlus2384.small2387,CompactPlus2384.nodes2387,NodePlus37.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus2384.p2388,GridPlus.atNode 2388,GridPlus.atNode 2389,NodePlus37.w20,CompactPlus2384.checked2388,CompactPlus2384.small2388,CompactPlus2384.nodes2388,NodePlus37.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus2384.p2389,GridPlus.atNode 2389,GridPlus.atNode 2390,NodePlus37.w21,CompactPlus2384.checked2389,CompactPlus2384.small2389,CompactPlus2384.nodes2389,NodePlus37.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus2384.p2390,GridPlus.atNode 2390,GridPlus.atNode 2391,NodePlus37.w22,CompactPlus2384.checked2390,CompactPlus2384.small2390,CompactPlus2384.nodes2390,NodePlus37.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus2384.p2391,GridPlus.atNode 2391,GridPlus.atNode 2392,NodePlus37.w23,CompactPlus2384.checked2391,CompactPlus2384.small2391,CompactPlus2384.nodes2391,NodePlus37.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus2384.p2392,GridPlus.atNode 2392,GridPlus.atNode 2393,NodePlus37.w24,CompactPlus2384.checked2392,CompactPlus2384.small2392,CompactPlus2384.nodes2392,NodePlus37.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus2384.p2393,GridPlus.atNode 2393,GridPlus.atNode 2394,NodePlus37.w25,CompactPlus2384.checked2393,CompactPlus2384.small2393,CompactPlus2384.nodes2393,NodePlus37.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus2384.p2394,GridPlus.atNode 2394,GridPlus.atNode 2395,NodePlus37.w26,CompactPlus2384.checked2394,CompactPlus2384.small2394,CompactPlus2384.nodes2394,NodePlus37.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus2384.p2395,GridPlus.atNode 2395,GridPlus.atNode 2396,NodePlus37.w27,CompactPlus2384.checked2395,CompactPlus2384.small2395,CompactPlus2384.nodes2395,NodePlus37.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus2384.p2396,GridPlus.atNode 2396,GridPlus.atNode 2397,NodePlus37.w28,CompactPlus2384.checked2396,CompactPlus2384.small2396,CompactPlus2384.nodes2396,NodePlus37.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus2384.p2397,GridPlus.atNode 2397,GridPlus.atNode 2398,NodePlus37.w29,CompactPlus2384.checked2397,CompactPlus2384.small2397,CompactPlus2384.nodes2397,NodePlus37.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus2384.p2398,GridPlus.atNode 2398,GridPlus.atNode 2399,NodePlus37.w30,CompactPlus2384.checked2398,CompactPlus2384.small2398,CompactPlus2384.nodes2398,NodePlus37.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus2384.p2399,GridPlus.atNode 2399,GridPlus.atNode 2400,NodePlus37.w31,CompactPlus2384.checked2399,CompactPlus2384.small2399,CompactPlus2384.nodes2399,NodePlus37.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus2400.p2400,GridPlus.atNode 2400,GridPlus.atNode 2401,NodePlus37.w32,CompactPlus2400.checked2400,CompactPlus2400.small2400,CompactPlus2400.nodes2400,NodePlus37.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus2400.p2401,GridPlus.atNode 2401,GridPlus.atNode 2402,NodePlus37.w33,CompactPlus2400.checked2401,CompactPlus2400.small2401,CompactPlus2400.nodes2401,NodePlus37.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus2400.p2402,GridPlus.atNode 2402,GridPlus.atNode 2403,NodePlus37.w34,CompactPlus2400.checked2402,CompactPlus2400.small2402,CompactPlus2400.nodes2402,NodePlus37.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus2400.p2403,GridPlus.atNode 2403,GridPlus.atNode 2404,NodePlus37.w35,CompactPlus2400.checked2403,CompactPlus2400.small2403,CompactPlus2400.nodes2403,NodePlus37.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus2400.p2404,GridPlus.atNode 2404,GridPlus.atNode 2405,NodePlus37.w36,CompactPlus2400.checked2404,CompactPlus2400.small2404,CompactPlus2400.nodes2404,NodePlus37.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus2400.p2405,GridPlus.atNode 2405,GridPlus.atNode 2406,NodePlus37.w37,CompactPlus2400.checked2405,CompactPlus2400.small2405,CompactPlus2400.nodes2405,NodePlus37.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus2400.p2406,GridPlus.atNode 2406,GridPlus.atNode 2407,NodePlus37.w38,CompactPlus2400.checked2406,CompactPlus2400.small2406,CompactPlus2400.nodes2406,NodePlus37.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus2400.p2407,GridPlus.atNode 2407,GridPlus.atNode 2408,NodePlus37.w39,CompactPlus2400.checked2407,CompactPlus2400.small2407,CompactPlus2400.nodes2407,NodePlus37.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus2400.p2408,GridPlus.atNode 2408,GridPlus.atNode 2409,NodePlus37.w40,CompactPlus2400.checked2408,CompactPlus2400.small2408,CompactPlus2400.nodes2408,NodePlus37.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus2400.p2409,GridPlus.atNode 2409,GridPlus.atNode 2410,NodePlus37.w41,CompactPlus2400.checked2409,CompactPlus2400.small2409,CompactPlus2400.nodes2409,NodePlus37.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus2400.p2410,GridPlus.atNode 2410,GridPlus.atNode 2411,NodePlus37.w42,CompactPlus2400.checked2410,CompactPlus2400.small2410,CompactPlus2400.nodes2410,NodePlus37.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus2400.p2411,GridPlus.atNode 2411,GridPlus.atNode 2412,NodePlus37.w43,CompactPlus2400.checked2411,CompactPlus2400.small2411,CompactPlus2400.nodes2411,NodePlus37.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus2400.p2412,GridPlus.atNode 2412,GridPlus.atNode 2413,NodePlus37.w44,CompactPlus2400.checked2412,CompactPlus2400.small2412,CompactPlus2400.nodes2412,NodePlus37.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus2400.p2413,GridPlus.atNode 2413,GridPlus.atNode 2414,NodePlus37.w45,CompactPlus2400.checked2413,CompactPlus2400.small2413,CompactPlus2400.nodes2413,NodePlus37.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus2400.p2414,GridPlus.atNode 2414,GridPlus.atNode 2415,NodePlus37.w46,CompactPlus2400.checked2414,CompactPlus2400.small2414,CompactPlus2400.nodes2414,NodePlus37.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus2400.p2415,GridPlus.atNode 2415,GridPlus.atNode 2416,NodePlus37.w47,CompactPlus2400.checked2415,CompactPlus2400.small2415,CompactPlus2400.nodes2415,NodePlus37.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus2416.p2416,GridPlus.atNode 2416,GridPlus.atNode 2417,NodePlus37.w48,CompactPlus2416.checked2416,CompactPlus2416.small2416,CompactPlus2416.nodes2416,NodePlus37.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus2416.p2417,GridPlus.atNode 2417,GridPlus.atNode 2418,NodePlus37.w49,CompactPlus2416.checked2417,CompactPlus2416.small2417,CompactPlus2416.nodes2417,NodePlus37.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus2416.p2418,GridPlus.atNode 2418,GridPlus.atNode 2419,NodePlus37.w50,CompactPlus2416.checked2418,CompactPlus2416.small2418,CompactPlus2416.nodes2418,NodePlus37.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus2416.p2419,GridPlus.atNode 2419,GridPlus.atNode 2420,NodePlus37.w51,CompactPlus2416.checked2419,CompactPlus2416.small2419,CompactPlus2416.nodes2419,NodePlus37.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus2416.p2420,GridPlus.atNode 2420,GridPlus.atNode 2421,NodePlus37.w52,CompactPlus2416.checked2420,CompactPlus2416.small2420,CompactPlus2416.nodes2420,NodePlus37.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus2416.p2421,GridPlus.atNode 2421,GridPlus.atNode 2422,NodePlus37.w53,CompactPlus2416.checked2421,CompactPlus2416.small2421,CompactPlus2416.nodes2421,NodePlus37.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus2416.p2422,GridPlus.atNode 2422,GridPlus.atNode 2423,NodePlus37.w54,CompactPlus2416.checked2422,CompactPlus2416.small2422,CompactPlus2416.nodes2422,NodePlus37.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus2416.p2423,GridPlus.atNode 2423,GridPlus.atNode 2424,NodePlus37.w55,CompactPlus2416.checked2423,CompactPlus2416.small2423,CompactPlus2416.nodes2423,NodePlus37.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus2416.p2424,GridPlus.atNode 2424,GridPlus.atNode 2425,NodePlus37.w56,CompactPlus2416.checked2424,CompactPlus2416.small2424,CompactPlus2416.nodes2424,NodePlus37.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus2416.p2425,GridPlus.atNode 2425,GridPlus.atNode 2426,NodePlus37.w57,CompactPlus2416.checked2425,CompactPlus2416.small2425,CompactPlus2416.nodes2425,NodePlus37.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus2416.p2426,GridPlus.atNode 2426,GridPlus.atNode 2427,NodePlus37.w58,CompactPlus2416.checked2426,CompactPlus2416.small2426,CompactPlus2416.nodes2426,NodePlus37.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus2416.p2427,GridPlus.atNode 2427,GridPlus.atNode 2428,NodePlus37.w59,CompactPlus2416.checked2427,CompactPlus2416.small2427,CompactPlus2416.nodes2427,NodePlus37.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus2416.p2428,GridPlus.atNode 2428,GridPlus.atNode 2429,NodePlus37.w60,CompactPlus2416.checked2428,CompactPlus2416.small2428,CompactPlus2416.nodes2428,NodePlus37.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus2416.p2429,GridPlus.atNode 2429,GridPlus.atNode 2430,NodePlus37.w61,CompactPlus2416.checked2429,CompactPlus2416.small2429,CompactPlus2416.nodes2429,NodePlus37.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus2416.p2430,GridPlus.atNode 2430,GridPlus.atNode 2431,NodePlus37.w62,CompactPlus2416.checked2430,CompactPlus2416.small2430,CompactPlus2416.nodes2430,NodePlus37.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus2416.p2431,GridPlus.atNode 2431,GridPlus.atNode 2432,NodePlus37.w63,CompactPlus2416.checked2431,CompactPlus2416.small2431,CompactPlus2416.nodes2431,NodePlus37.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (2368+j) ∧
    (atRow j).right=GridPlus.atNode (2368+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus37
