import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus2432
import SolitonClassification.Rotating.ResetPackedMinus2448
import SolitonClassification.Rotating.ResetPackedMinus2464
import SolitonClassification.Rotating.ResetPackedMinus2480
namespace SolitonClassification.Rotating.DyadicReset.TileMinus38
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2432.p2432,GridMinus.atNode 2432,GridMinus.atNode 2433,NodeMinus38.w0,CompactMinus2432.checked2432,CompactMinus2432.small2432,CompactMinus2432.nodes2432,NodeMinus38.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2432.p2433,GridMinus.atNode 2433,GridMinus.atNode 2434,NodeMinus38.w1,CompactMinus2432.checked2433,CompactMinus2432.small2433,CompactMinus2432.nodes2433,NodeMinus38.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2432.p2434,GridMinus.atNode 2434,GridMinus.atNode 2435,NodeMinus38.w2,CompactMinus2432.checked2434,CompactMinus2432.small2434,CompactMinus2432.nodes2434,NodeMinus38.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2432.p2435,GridMinus.atNode 2435,GridMinus.atNode 2436,NodeMinus38.w3,CompactMinus2432.checked2435,CompactMinus2432.small2435,CompactMinus2432.nodes2435,NodeMinus38.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2432.p2436,GridMinus.atNode 2436,GridMinus.atNode 2437,NodeMinus38.w4,CompactMinus2432.checked2436,CompactMinus2432.small2436,CompactMinus2432.nodes2436,NodeMinus38.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2432.p2437,GridMinus.atNode 2437,GridMinus.atNode 2438,NodeMinus38.w5,CompactMinus2432.checked2437,CompactMinus2432.small2437,CompactMinus2432.nodes2437,NodeMinus38.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2432.p2438,GridMinus.atNode 2438,GridMinus.atNode 2439,NodeMinus38.w6,CompactMinus2432.checked2438,CompactMinus2432.small2438,CompactMinus2432.nodes2438,NodeMinus38.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2432.p2439,GridMinus.atNode 2439,GridMinus.atNode 2440,NodeMinus38.w7,CompactMinus2432.checked2439,CompactMinus2432.small2439,CompactMinus2432.nodes2439,NodeMinus38.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2432.p2440,GridMinus.atNode 2440,GridMinus.atNode 2441,NodeMinus38.w8,CompactMinus2432.checked2440,CompactMinus2432.small2440,CompactMinus2432.nodes2440,NodeMinus38.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2432.p2441,GridMinus.atNode 2441,GridMinus.atNode 2442,NodeMinus38.w9,CompactMinus2432.checked2441,CompactMinus2432.small2441,CompactMinus2432.nodes2441,NodeMinus38.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2432.p2442,GridMinus.atNode 2442,GridMinus.atNode 2443,NodeMinus38.w10,CompactMinus2432.checked2442,CompactMinus2432.small2442,CompactMinus2432.nodes2442,NodeMinus38.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2432.p2443,GridMinus.atNode 2443,GridMinus.atNode 2444,NodeMinus38.w11,CompactMinus2432.checked2443,CompactMinus2432.small2443,CompactMinus2432.nodes2443,NodeMinus38.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2432.p2444,GridMinus.atNode 2444,GridMinus.atNode 2445,NodeMinus38.w12,CompactMinus2432.checked2444,CompactMinus2432.small2444,CompactMinus2432.nodes2444,NodeMinus38.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2432.p2445,GridMinus.atNode 2445,GridMinus.atNode 2446,NodeMinus38.w13,CompactMinus2432.checked2445,CompactMinus2432.small2445,CompactMinus2432.nodes2445,NodeMinus38.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2432.p2446,GridMinus.atNode 2446,GridMinus.atNode 2447,NodeMinus38.w14,CompactMinus2432.checked2446,CompactMinus2432.small2446,CompactMinus2432.nodes2446,NodeMinus38.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2432.p2447,GridMinus.atNode 2447,GridMinus.atNode 2448,NodeMinus38.w15,CompactMinus2432.checked2447,CompactMinus2432.small2447,CompactMinus2432.nodes2447,NodeMinus38.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2448.p2448,GridMinus.atNode 2448,GridMinus.atNode 2449,NodeMinus38.w16,CompactMinus2448.checked2448,CompactMinus2448.small2448,CompactMinus2448.nodes2448,NodeMinus38.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2448.p2449,GridMinus.atNode 2449,GridMinus.atNode 2450,NodeMinus38.w17,CompactMinus2448.checked2449,CompactMinus2448.small2449,CompactMinus2448.nodes2449,NodeMinus38.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2448.p2450,GridMinus.atNode 2450,GridMinus.atNode 2451,NodeMinus38.w18,CompactMinus2448.checked2450,CompactMinus2448.small2450,CompactMinus2448.nodes2450,NodeMinus38.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2448.p2451,GridMinus.atNode 2451,GridMinus.atNode 2452,NodeMinus38.w19,CompactMinus2448.checked2451,CompactMinus2448.small2451,CompactMinus2448.nodes2451,NodeMinus38.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2448.p2452,GridMinus.atNode 2452,GridMinus.atNode 2453,NodeMinus38.w20,CompactMinus2448.checked2452,CompactMinus2448.small2452,CompactMinus2448.nodes2452,NodeMinus38.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2448.p2453,GridMinus.atNode 2453,GridMinus.atNode 2454,NodeMinus38.w21,CompactMinus2448.checked2453,CompactMinus2448.small2453,CompactMinus2448.nodes2453,NodeMinus38.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2448.p2454,GridMinus.atNode 2454,GridMinus.atNode 2455,NodeMinus38.w22,CompactMinus2448.checked2454,CompactMinus2448.small2454,CompactMinus2448.nodes2454,NodeMinus38.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2448.p2455,GridMinus.atNode 2455,GridMinus.atNode 2456,NodeMinus38.w23,CompactMinus2448.checked2455,CompactMinus2448.small2455,CompactMinus2448.nodes2455,NodeMinus38.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2448.p2456,GridMinus.atNode 2456,GridMinus.atNode 2457,NodeMinus38.w24,CompactMinus2448.checked2456,CompactMinus2448.small2456,CompactMinus2448.nodes2456,NodeMinus38.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2448.p2457,GridMinus.atNode 2457,GridMinus.atNode 2458,NodeMinus38.w25,CompactMinus2448.checked2457,CompactMinus2448.small2457,CompactMinus2448.nodes2457,NodeMinus38.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2448.p2458,GridMinus.atNode 2458,GridMinus.atNode 2459,NodeMinus38.w26,CompactMinus2448.checked2458,CompactMinus2448.small2458,CompactMinus2448.nodes2458,NodeMinus38.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2448.p2459,GridMinus.atNode 2459,GridMinus.atNode 2460,NodeMinus38.w27,CompactMinus2448.checked2459,CompactMinus2448.small2459,CompactMinus2448.nodes2459,NodeMinus38.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2448.p2460,GridMinus.atNode 2460,GridMinus.atNode 2461,NodeMinus38.w28,CompactMinus2448.checked2460,CompactMinus2448.small2460,CompactMinus2448.nodes2460,NodeMinus38.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2448.p2461,GridMinus.atNode 2461,GridMinus.atNode 2462,NodeMinus38.w29,CompactMinus2448.checked2461,CompactMinus2448.small2461,CompactMinus2448.nodes2461,NodeMinus38.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2448.p2462,GridMinus.atNode 2462,GridMinus.atNode 2463,NodeMinus38.w30,CompactMinus2448.checked2462,CompactMinus2448.small2462,CompactMinus2448.nodes2462,NodeMinus38.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2448.p2463,GridMinus.atNode 2463,GridMinus.atNode 2464,NodeMinus38.w31,CompactMinus2448.checked2463,CompactMinus2448.small2463,CompactMinus2448.nodes2463,NodeMinus38.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2464.p2464,GridMinus.atNode 2464,GridMinus.atNode 2465,NodeMinus38.w32,CompactMinus2464.checked2464,CompactMinus2464.small2464,CompactMinus2464.nodes2464,NodeMinus38.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2464.p2465,GridMinus.atNode 2465,GridMinus.atNode 2466,NodeMinus38.w33,CompactMinus2464.checked2465,CompactMinus2464.small2465,CompactMinus2464.nodes2465,NodeMinus38.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2464.p2466,GridMinus.atNode 2466,GridMinus.atNode 2467,NodeMinus38.w34,CompactMinus2464.checked2466,CompactMinus2464.small2466,CompactMinus2464.nodes2466,NodeMinus38.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2464.p2467,GridMinus.atNode 2467,GridMinus.atNode 2468,NodeMinus38.w35,CompactMinus2464.checked2467,CompactMinus2464.small2467,CompactMinus2464.nodes2467,NodeMinus38.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2464.p2468,GridMinus.atNode 2468,GridMinus.atNode 2469,NodeMinus38.w36,CompactMinus2464.checked2468,CompactMinus2464.small2468,CompactMinus2464.nodes2468,NodeMinus38.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2464.p2469,GridMinus.atNode 2469,GridMinus.atNode 2470,NodeMinus38.w37,CompactMinus2464.checked2469,CompactMinus2464.small2469,CompactMinus2464.nodes2469,NodeMinus38.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2464.p2470,GridMinus.atNode 2470,GridMinus.atNode 2471,NodeMinus38.w38,CompactMinus2464.checked2470,CompactMinus2464.small2470,CompactMinus2464.nodes2470,NodeMinus38.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2464.p2471,GridMinus.atNode 2471,GridMinus.atNode 2472,NodeMinus38.w39,CompactMinus2464.checked2471,CompactMinus2464.small2471,CompactMinus2464.nodes2471,NodeMinus38.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2464.p2472,GridMinus.atNode 2472,GridMinus.atNode 2473,NodeMinus38.w40,CompactMinus2464.checked2472,CompactMinus2464.small2472,CompactMinus2464.nodes2472,NodeMinus38.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2464.p2473,GridMinus.atNode 2473,GridMinus.atNode 2474,NodeMinus38.w41,CompactMinus2464.checked2473,CompactMinus2464.small2473,CompactMinus2464.nodes2473,NodeMinus38.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2464.p2474,GridMinus.atNode 2474,GridMinus.atNode 2475,NodeMinus38.w42,CompactMinus2464.checked2474,CompactMinus2464.small2474,CompactMinus2464.nodes2474,NodeMinus38.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2464.p2475,GridMinus.atNode 2475,GridMinus.atNode 2476,NodeMinus38.w43,CompactMinus2464.checked2475,CompactMinus2464.small2475,CompactMinus2464.nodes2475,NodeMinus38.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2464.p2476,GridMinus.atNode 2476,GridMinus.atNode 2477,NodeMinus38.w44,CompactMinus2464.checked2476,CompactMinus2464.small2476,CompactMinus2464.nodes2476,NodeMinus38.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2464.p2477,GridMinus.atNode 2477,GridMinus.atNode 2478,NodeMinus38.w45,CompactMinus2464.checked2477,CompactMinus2464.small2477,CompactMinus2464.nodes2477,NodeMinus38.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2464.p2478,GridMinus.atNode 2478,GridMinus.atNode 2479,NodeMinus38.w46,CompactMinus2464.checked2478,CompactMinus2464.small2478,CompactMinus2464.nodes2478,NodeMinus38.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2464.p2479,GridMinus.atNode 2479,GridMinus.atNode 2480,NodeMinus38.w47,CompactMinus2464.checked2479,CompactMinus2464.small2479,CompactMinus2464.nodes2479,NodeMinus38.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2480.p2480,GridMinus.atNode 2480,GridMinus.atNode 2481,NodeMinus38.w48,CompactMinus2480.checked2480,CompactMinus2480.small2480,CompactMinus2480.nodes2480,NodeMinus38.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2480.p2481,GridMinus.atNode 2481,GridMinus.atNode 2482,NodeMinus38.w49,CompactMinus2480.checked2481,CompactMinus2480.small2481,CompactMinus2480.nodes2481,NodeMinus38.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2480.p2482,GridMinus.atNode 2482,GridMinus.atNode 2483,NodeMinus38.w50,CompactMinus2480.checked2482,CompactMinus2480.small2482,CompactMinus2480.nodes2482,NodeMinus38.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2480.p2483,GridMinus.atNode 2483,GridMinus.atNode 2484,NodeMinus38.w51,CompactMinus2480.checked2483,CompactMinus2480.small2483,CompactMinus2480.nodes2483,NodeMinus38.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2480.p2484,GridMinus.atNode 2484,GridMinus.atNode 2485,NodeMinus38.w52,CompactMinus2480.checked2484,CompactMinus2480.small2484,CompactMinus2480.nodes2484,NodeMinus38.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2480.p2485,GridMinus.atNode 2485,GridMinus.atNode 2486,NodeMinus38.w53,CompactMinus2480.checked2485,CompactMinus2480.small2485,CompactMinus2480.nodes2485,NodeMinus38.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2480.p2486,GridMinus.atNode 2486,GridMinus.atNode 2487,NodeMinus38.w54,CompactMinus2480.checked2486,CompactMinus2480.small2486,CompactMinus2480.nodes2486,NodeMinus38.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2480.p2487,GridMinus.atNode 2487,GridMinus.atNode 2488,NodeMinus38.w55,CompactMinus2480.checked2487,CompactMinus2480.small2487,CompactMinus2480.nodes2487,NodeMinus38.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2480.p2488,GridMinus.atNode 2488,GridMinus.atNode 2489,NodeMinus38.w56,CompactMinus2480.checked2488,CompactMinus2480.small2488,CompactMinus2480.nodes2488,NodeMinus38.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2480.p2489,GridMinus.atNode 2489,GridMinus.atNode 2490,NodeMinus38.w57,CompactMinus2480.checked2489,CompactMinus2480.small2489,CompactMinus2480.nodes2489,NodeMinus38.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2480.p2490,GridMinus.atNode 2490,GridMinus.atNode 2491,NodeMinus38.w58,CompactMinus2480.checked2490,CompactMinus2480.small2490,CompactMinus2480.nodes2490,NodeMinus38.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2480.p2491,GridMinus.atNode 2491,GridMinus.atNode 2492,NodeMinus38.w59,CompactMinus2480.checked2491,CompactMinus2480.small2491,CompactMinus2480.nodes2491,NodeMinus38.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2480.p2492,GridMinus.atNode 2492,GridMinus.atNode 2493,NodeMinus38.w60,CompactMinus2480.checked2492,CompactMinus2480.small2492,CompactMinus2480.nodes2492,NodeMinus38.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2480.p2493,GridMinus.atNode 2493,GridMinus.atNode 2494,NodeMinus38.w61,CompactMinus2480.checked2493,CompactMinus2480.small2493,CompactMinus2480.nodes2493,NodeMinus38.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2480.p2494,GridMinus.atNode 2494,GridMinus.atNode 2495,NodeMinus38.w62,CompactMinus2480.checked2494,CompactMinus2480.small2494,CompactMinus2480.nodes2494,NodeMinus38.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2480.p2495,GridMinus.atNode 2495,GridMinus.atNode 2496,NodeMinus38.w63,CompactMinus2480.checked2495,CompactMinus2480.small2495,CompactMinus2480.nodes2495,NodeMinus38.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (2432+j) ∧
    (atRow j).right=GridMinus.atNode (2432+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus38
