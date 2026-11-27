import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus2432
import SolitonClassification.Rotating.ResetPackedPlus2448
import SolitonClassification.Rotating.ResetPackedPlus2464
import SolitonClassification.Rotating.ResetPackedPlus2480
namespace SolitonClassification.Rotating.DyadicReset.TilePlus38
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus2432.p2432,GridPlus.atNode 2432,GridPlus.atNode 2433,NodePlus38.w0,CompactPlus2432.checked2432,CompactPlus2432.small2432,CompactPlus2432.nodes2432,NodePlus38.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus2432.p2433,GridPlus.atNode 2433,GridPlus.atNode 2434,NodePlus38.w1,CompactPlus2432.checked2433,CompactPlus2432.small2433,CompactPlus2432.nodes2433,NodePlus38.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus2432.p2434,GridPlus.atNode 2434,GridPlus.atNode 2435,NodePlus38.w2,CompactPlus2432.checked2434,CompactPlus2432.small2434,CompactPlus2432.nodes2434,NodePlus38.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus2432.p2435,GridPlus.atNode 2435,GridPlus.atNode 2436,NodePlus38.w3,CompactPlus2432.checked2435,CompactPlus2432.small2435,CompactPlus2432.nodes2435,NodePlus38.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus2432.p2436,GridPlus.atNode 2436,GridPlus.atNode 2437,NodePlus38.w4,CompactPlus2432.checked2436,CompactPlus2432.small2436,CompactPlus2432.nodes2436,NodePlus38.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus2432.p2437,GridPlus.atNode 2437,GridPlus.atNode 2438,NodePlus38.w5,CompactPlus2432.checked2437,CompactPlus2432.small2437,CompactPlus2432.nodes2437,NodePlus38.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus2432.p2438,GridPlus.atNode 2438,GridPlus.atNode 2439,NodePlus38.w6,CompactPlus2432.checked2438,CompactPlus2432.small2438,CompactPlus2432.nodes2438,NodePlus38.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus2432.p2439,GridPlus.atNode 2439,GridPlus.atNode 2440,NodePlus38.w7,CompactPlus2432.checked2439,CompactPlus2432.small2439,CompactPlus2432.nodes2439,NodePlus38.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus2432.p2440,GridPlus.atNode 2440,GridPlus.atNode 2441,NodePlus38.w8,CompactPlus2432.checked2440,CompactPlus2432.small2440,CompactPlus2432.nodes2440,NodePlus38.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus2432.p2441,GridPlus.atNode 2441,GridPlus.atNode 2442,NodePlus38.w9,CompactPlus2432.checked2441,CompactPlus2432.small2441,CompactPlus2432.nodes2441,NodePlus38.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus2432.p2442,GridPlus.atNode 2442,GridPlus.atNode 2443,NodePlus38.w10,CompactPlus2432.checked2442,CompactPlus2432.small2442,CompactPlus2432.nodes2442,NodePlus38.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus2432.p2443,GridPlus.atNode 2443,GridPlus.atNode 2444,NodePlus38.w11,CompactPlus2432.checked2443,CompactPlus2432.small2443,CompactPlus2432.nodes2443,NodePlus38.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus2432.p2444,GridPlus.atNode 2444,GridPlus.atNode 2445,NodePlus38.w12,CompactPlus2432.checked2444,CompactPlus2432.small2444,CompactPlus2432.nodes2444,NodePlus38.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus2432.p2445,GridPlus.atNode 2445,GridPlus.atNode 2446,NodePlus38.w13,CompactPlus2432.checked2445,CompactPlus2432.small2445,CompactPlus2432.nodes2445,NodePlus38.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus2432.p2446,GridPlus.atNode 2446,GridPlus.atNode 2447,NodePlus38.w14,CompactPlus2432.checked2446,CompactPlus2432.small2446,CompactPlus2432.nodes2446,NodePlus38.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus2432.p2447,GridPlus.atNode 2447,GridPlus.atNode 2448,NodePlus38.w15,CompactPlus2432.checked2447,CompactPlus2432.small2447,CompactPlus2432.nodes2447,NodePlus38.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus2448.p2448,GridPlus.atNode 2448,GridPlus.atNode 2449,NodePlus38.w16,CompactPlus2448.checked2448,CompactPlus2448.small2448,CompactPlus2448.nodes2448,NodePlus38.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus2448.p2449,GridPlus.atNode 2449,GridPlus.atNode 2450,NodePlus38.w17,CompactPlus2448.checked2449,CompactPlus2448.small2449,CompactPlus2448.nodes2449,NodePlus38.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus2448.p2450,GridPlus.atNode 2450,GridPlus.atNode 2451,NodePlus38.w18,CompactPlus2448.checked2450,CompactPlus2448.small2450,CompactPlus2448.nodes2450,NodePlus38.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus2448.p2451,GridPlus.atNode 2451,GridPlus.atNode 2452,NodePlus38.w19,CompactPlus2448.checked2451,CompactPlus2448.small2451,CompactPlus2448.nodes2451,NodePlus38.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus2448.p2452,GridPlus.atNode 2452,GridPlus.atNode 2453,NodePlus38.w20,CompactPlus2448.checked2452,CompactPlus2448.small2452,CompactPlus2448.nodes2452,NodePlus38.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus2448.p2453,GridPlus.atNode 2453,GridPlus.atNode 2454,NodePlus38.w21,CompactPlus2448.checked2453,CompactPlus2448.small2453,CompactPlus2448.nodes2453,NodePlus38.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus2448.p2454,GridPlus.atNode 2454,GridPlus.atNode 2455,NodePlus38.w22,CompactPlus2448.checked2454,CompactPlus2448.small2454,CompactPlus2448.nodes2454,NodePlus38.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus2448.p2455,GridPlus.atNode 2455,GridPlus.atNode 2456,NodePlus38.w23,CompactPlus2448.checked2455,CompactPlus2448.small2455,CompactPlus2448.nodes2455,NodePlus38.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus2448.p2456,GridPlus.atNode 2456,GridPlus.atNode 2457,NodePlus38.w24,CompactPlus2448.checked2456,CompactPlus2448.small2456,CompactPlus2448.nodes2456,NodePlus38.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus2448.p2457,GridPlus.atNode 2457,GridPlus.atNode 2458,NodePlus38.w25,CompactPlus2448.checked2457,CompactPlus2448.small2457,CompactPlus2448.nodes2457,NodePlus38.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus2448.p2458,GridPlus.atNode 2458,GridPlus.atNode 2459,NodePlus38.w26,CompactPlus2448.checked2458,CompactPlus2448.small2458,CompactPlus2448.nodes2458,NodePlus38.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus2448.p2459,GridPlus.atNode 2459,GridPlus.atNode 2460,NodePlus38.w27,CompactPlus2448.checked2459,CompactPlus2448.small2459,CompactPlus2448.nodes2459,NodePlus38.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus2448.p2460,GridPlus.atNode 2460,GridPlus.atNode 2461,NodePlus38.w28,CompactPlus2448.checked2460,CompactPlus2448.small2460,CompactPlus2448.nodes2460,NodePlus38.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus2448.p2461,GridPlus.atNode 2461,GridPlus.atNode 2462,NodePlus38.w29,CompactPlus2448.checked2461,CompactPlus2448.small2461,CompactPlus2448.nodes2461,NodePlus38.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus2448.p2462,GridPlus.atNode 2462,GridPlus.atNode 2463,NodePlus38.w30,CompactPlus2448.checked2462,CompactPlus2448.small2462,CompactPlus2448.nodes2462,NodePlus38.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus2448.p2463,GridPlus.atNode 2463,GridPlus.atNode 2464,NodePlus38.w31,CompactPlus2448.checked2463,CompactPlus2448.small2463,CompactPlus2448.nodes2463,NodePlus38.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus2464.p2464,GridPlus.atNode 2464,GridPlus.atNode 2465,NodePlus38.w32,CompactPlus2464.checked2464,CompactPlus2464.small2464,CompactPlus2464.nodes2464,NodePlus38.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus2464.p2465,GridPlus.atNode 2465,GridPlus.atNode 2466,NodePlus38.w33,CompactPlus2464.checked2465,CompactPlus2464.small2465,CompactPlus2464.nodes2465,NodePlus38.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus2464.p2466,GridPlus.atNode 2466,GridPlus.atNode 2467,NodePlus38.w34,CompactPlus2464.checked2466,CompactPlus2464.small2466,CompactPlus2464.nodes2466,NodePlus38.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus2464.p2467,GridPlus.atNode 2467,GridPlus.atNode 2468,NodePlus38.w35,CompactPlus2464.checked2467,CompactPlus2464.small2467,CompactPlus2464.nodes2467,NodePlus38.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus2464.p2468,GridPlus.atNode 2468,GridPlus.atNode 2469,NodePlus38.w36,CompactPlus2464.checked2468,CompactPlus2464.small2468,CompactPlus2464.nodes2468,NodePlus38.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus2464.p2469,GridPlus.atNode 2469,GridPlus.atNode 2470,NodePlus38.w37,CompactPlus2464.checked2469,CompactPlus2464.small2469,CompactPlus2464.nodes2469,NodePlus38.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus2464.p2470,GridPlus.atNode 2470,GridPlus.atNode 2471,NodePlus38.w38,CompactPlus2464.checked2470,CompactPlus2464.small2470,CompactPlus2464.nodes2470,NodePlus38.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus2464.p2471,GridPlus.atNode 2471,GridPlus.atNode 2472,NodePlus38.w39,CompactPlus2464.checked2471,CompactPlus2464.small2471,CompactPlus2464.nodes2471,NodePlus38.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus2464.p2472,GridPlus.atNode 2472,GridPlus.atNode 2473,NodePlus38.w40,CompactPlus2464.checked2472,CompactPlus2464.small2472,CompactPlus2464.nodes2472,NodePlus38.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus2464.p2473,GridPlus.atNode 2473,GridPlus.atNode 2474,NodePlus38.w41,CompactPlus2464.checked2473,CompactPlus2464.small2473,CompactPlus2464.nodes2473,NodePlus38.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus2464.p2474,GridPlus.atNode 2474,GridPlus.atNode 2475,NodePlus38.w42,CompactPlus2464.checked2474,CompactPlus2464.small2474,CompactPlus2464.nodes2474,NodePlus38.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus2464.p2475,GridPlus.atNode 2475,GridPlus.atNode 2476,NodePlus38.w43,CompactPlus2464.checked2475,CompactPlus2464.small2475,CompactPlus2464.nodes2475,NodePlus38.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus2464.p2476,GridPlus.atNode 2476,GridPlus.atNode 2477,NodePlus38.w44,CompactPlus2464.checked2476,CompactPlus2464.small2476,CompactPlus2464.nodes2476,NodePlus38.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus2464.p2477,GridPlus.atNode 2477,GridPlus.atNode 2478,NodePlus38.w45,CompactPlus2464.checked2477,CompactPlus2464.small2477,CompactPlus2464.nodes2477,NodePlus38.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus2464.p2478,GridPlus.atNode 2478,GridPlus.atNode 2479,NodePlus38.w46,CompactPlus2464.checked2478,CompactPlus2464.small2478,CompactPlus2464.nodes2478,NodePlus38.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus2464.p2479,GridPlus.atNode 2479,GridPlus.atNode 2480,NodePlus38.w47,CompactPlus2464.checked2479,CompactPlus2464.small2479,CompactPlus2464.nodes2479,NodePlus38.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus2480.p2480,GridPlus.atNode 2480,GridPlus.atNode 2481,NodePlus38.w48,CompactPlus2480.checked2480,CompactPlus2480.small2480,CompactPlus2480.nodes2480,NodePlus38.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus2480.p2481,GridPlus.atNode 2481,GridPlus.atNode 2482,NodePlus38.w49,CompactPlus2480.checked2481,CompactPlus2480.small2481,CompactPlus2480.nodes2481,NodePlus38.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus2480.p2482,GridPlus.atNode 2482,GridPlus.atNode 2483,NodePlus38.w50,CompactPlus2480.checked2482,CompactPlus2480.small2482,CompactPlus2480.nodes2482,NodePlus38.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus2480.p2483,GridPlus.atNode 2483,GridPlus.atNode 2484,NodePlus38.w51,CompactPlus2480.checked2483,CompactPlus2480.small2483,CompactPlus2480.nodes2483,NodePlus38.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus2480.p2484,GridPlus.atNode 2484,GridPlus.atNode 2485,NodePlus38.w52,CompactPlus2480.checked2484,CompactPlus2480.small2484,CompactPlus2480.nodes2484,NodePlus38.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus2480.p2485,GridPlus.atNode 2485,GridPlus.atNode 2486,NodePlus38.w53,CompactPlus2480.checked2485,CompactPlus2480.small2485,CompactPlus2480.nodes2485,NodePlus38.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus2480.p2486,GridPlus.atNode 2486,GridPlus.atNode 2487,NodePlus38.w54,CompactPlus2480.checked2486,CompactPlus2480.small2486,CompactPlus2480.nodes2486,NodePlus38.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus2480.p2487,GridPlus.atNode 2487,GridPlus.atNode 2488,NodePlus38.w55,CompactPlus2480.checked2487,CompactPlus2480.small2487,CompactPlus2480.nodes2487,NodePlus38.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus2480.p2488,GridPlus.atNode 2488,GridPlus.atNode 2489,NodePlus38.w56,CompactPlus2480.checked2488,CompactPlus2480.small2488,CompactPlus2480.nodes2488,NodePlus38.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus2480.p2489,GridPlus.atNode 2489,GridPlus.atNode 2490,NodePlus38.w57,CompactPlus2480.checked2489,CompactPlus2480.small2489,CompactPlus2480.nodes2489,NodePlus38.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus2480.p2490,GridPlus.atNode 2490,GridPlus.atNode 2491,NodePlus38.w58,CompactPlus2480.checked2490,CompactPlus2480.small2490,CompactPlus2480.nodes2490,NodePlus38.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus2480.p2491,GridPlus.atNode 2491,GridPlus.atNode 2492,NodePlus38.w59,CompactPlus2480.checked2491,CompactPlus2480.small2491,CompactPlus2480.nodes2491,NodePlus38.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus2480.p2492,GridPlus.atNode 2492,GridPlus.atNode 2493,NodePlus38.w60,CompactPlus2480.checked2492,CompactPlus2480.small2492,CompactPlus2480.nodes2492,NodePlus38.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus2480.p2493,GridPlus.atNode 2493,GridPlus.atNode 2494,NodePlus38.w61,CompactPlus2480.checked2493,CompactPlus2480.small2493,CompactPlus2480.nodes2493,NodePlus38.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus2480.p2494,GridPlus.atNode 2494,GridPlus.atNode 2495,NodePlus38.w62,CompactPlus2480.checked2494,CompactPlus2480.small2494,CompactPlus2480.nodes2494,NodePlus38.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus2480.p2495,GridPlus.atNode 2495,GridPlus.atNode 2496,NodePlus38.w63,CompactPlus2480.checked2495,CompactPlus2480.small2495,CompactPlus2480.nodes2495,NodePlus38.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (2432+j) ∧
    (atRow j).right=GridPlus.atNode (2432+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus38
