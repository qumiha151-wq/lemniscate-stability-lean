import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus2496
import SolitonClassification.Rotating.ResetPackedMinus2512
import SolitonClassification.Rotating.ResetPackedMinus2528
import SolitonClassification.Rotating.ResetPackedMinus2544
namespace SolitonClassification.Rotating.DyadicReset.TileMinus39
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2496.p2496,GridMinus.atNode 2496,GridMinus.atNode 2497,NodeMinus39.w0,CompactMinus2496.checked2496,CompactMinus2496.small2496,CompactMinus2496.nodes2496,NodeMinus39.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2496.p2497,GridMinus.atNode 2497,GridMinus.atNode 2498,NodeMinus39.w1,CompactMinus2496.checked2497,CompactMinus2496.small2497,CompactMinus2496.nodes2497,NodeMinus39.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2496.p2498,GridMinus.atNode 2498,GridMinus.atNode 2499,NodeMinus39.w2,CompactMinus2496.checked2498,CompactMinus2496.small2498,CompactMinus2496.nodes2498,NodeMinus39.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2496.p2499,GridMinus.atNode 2499,GridMinus.atNode 2500,NodeMinus39.w3,CompactMinus2496.checked2499,CompactMinus2496.small2499,CompactMinus2496.nodes2499,NodeMinus39.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2496.p2500,GridMinus.atNode 2500,GridMinus.atNode 2501,NodeMinus39.w4,CompactMinus2496.checked2500,CompactMinus2496.small2500,CompactMinus2496.nodes2500,NodeMinus39.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2496.p2501,GridMinus.atNode 2501,GridMinus.atNode 2502,NodeMinus39.w5,CompactMinus2496.checked2501,CompactMinus2496.small2501,CompactMinus2496.nodes2501,NodeMinus39.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2496.p2502,GridMinus.atNode 2502,GridMinus.atNode 2503,NodeMinus39.w6,CompactMinus2496.checked2502,CompactMinus2496.small2502,CompactMinus2496.nodes2502,NodeMinus39.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2496.p2503,GridMinus.atNode 2503,GridMinus.atNode 2504,NodeMinus39.w7,CompactMinus2496.checked2503,CompactMinus2496.small2503,CompactMinus2496.nodes2503,NodeMinus39.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2496.p2504,GridMinus.atNode 2504,GridMinus.atNode 2505,NodeMinus39.w8,CompactMinus2496.checked2504,CompactMinus2496.small2504,CompactMinus2496.nodes2504,NodeMinus39.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2496.p2505,GridMinus.atNode 2505,GridMinus.atNode 2506,NodeMinus39.w9,CompactMinus2496.checked2505,CompactMinus2496.small2505,CompactMinus2496.nodes2505,NodeMinus39.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2496.p2506,GridMinus.atNode 2506,GridMinus.atNode 2507,NodeMinus39.w10,CompactMinus2496.checked2506,CompactMinus2496.small2506,CompactMinus2496.nodes2506,NodeMinus39.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2496.p2507,GridMinus.atNode 2507,GridMinus.atNode 2508,NodeMinus39.w11,CompactMinus2496.checked2507,CompactMinus2496.small2507,CompactMinus2496.nodes2507,NodeMinus39.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2496.p2508,GridMinus.atNode 2508,GridMinus.atNode 2509,NodeMinus39.w12,CompactMinus2496.checked2508,CompactMinus2496.small2508,CompactMinus2496.nodes2508,NodeMinus39.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2496.p2509,GridMinus.atNode 2509,GridMinus.atNode 2510,NodeMinus39.w13,CompactMinus2496.checked2509,CompactMinus2496.small2509,CompactMinus2496.nodes2509,NodeMinus39.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2496.p2510,GridMinus.atNode 2510,GridMinus.atNode 2511,NodeMinus39.w14,CompactMinus2496.checked2510,CompactMinus2496.small2510,CompactMinus2496.nodes2510,NodeMinus39.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2496.p2511,GridMinus.atNode 2511,GridMinus.atNode 2512,NodeMinus39.w15,CompactMinus2496.checked2511,CompactMinus2496.small2511,CompactMinus2496.nodes2511,NodeMinus39.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2512.p2512,GridMinus.atNode 2512,GridMinus.atNode 2513,NodeMinus39.w16,CompactMinus2512.checked2512,CompactMinus2512.small2512,CompactMinus2512.nodes2512,NodeMinus39.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2512.p2513,GridMinus.atNode 2513,GridMinus.atNode 2514,NodeMinus39.w17,CompactMinus2512.checked2513,CompactMinus2512.small2513,CompactMinus2512.nodes2513,NodeMinus39.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2512.p2514,GridMinus.atNode 2514,GridMinus.atNode 2515,NodeMinus39.w18,CompactMinus2512.checked2514,CompactMinus2512.small2514,CompactMinus2512.nodes2514,NodeMinus39.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2512.p2515,GridMinus.atNode 2515,GridMinus.atNode 2516,NodeMinus39.w19,CompactMinus2512.checked2515,CompactMinus2512.small2515,CompactMinus2512.nodes2515,NodeMinus39.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2512.p2516,GridMinus.atNode 2516,GridMinus.atNode 2517,NodeMinus39.w20,CompactMinus2512.checked2516,CompactMinus2512.small2516,CompactMinus2512.nodes2516,NodeMinus39.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2512.p2517,GridMinus.atNode 2517,GridMinus.atNode 2518,NodeMinus39.w21,CompactMinus2512.checked2517,CompactMinus2512.small2517,CompactMinus2512.nodes2517,NodeMinus39.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2512.p2518,GridMinus.atNode 2518,GridMinus.atNode 2519,NodeMinus39.w22,CompactMinus2512.checked2518,CompactMinus2512.small2518,CompactMinus2512.nodes2518,NodeMinus39.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2512.p2519,GridMinus.atNode 2519,GridMinus.atNode 2520,NodeMinus39.w23,CompactMinus2512.checked2519,CompactMinus2512.small2519,CompactMinus2512.nodes2519,NodeMinus39.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2512.p2520,GridMinus.atNode 2520,GridMinus.atNode 2521,NodeMinus39.w24,CompactMinus2512.checked2520,CompactMinus2512.small2520,CompactMinus2512.nodes2520,NodeMinus39.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2512.p2521,GridMinus.atNode 2521,GridMinus.atNode 2522,NodeMinus39.w25,CompactMinus2512.checked2521,CompactMinus2512.small2521,CompactMinus2512.nodes2521,NodeMinus39.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2512.p2522,GridMinus.atNode 2522,GridMinus.atNode 2523,NodeMinus39.w26,CompactMinus2512.checked2522,CompactMinus2512.small2522,CompactMinus2512.nodes2522,NodeMinus39.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2512.p2523,GridMinus.atNode 2523,GridMinus.atNode 2524,NodeMinus39.w27,CompactMinus2512.checked2523,CompactMinus2512.small2523,CompactMinus2512.nodes2523,NodeMinus39.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2512.p2524,GridMinus.atNode 2524,GridMinus.atNode 2525,NodeMinus39.w28,CompactMinus2512.checked2524,CompactMinus2512.small2524,CompactMinus2512.nodes2524,NodeMinus39.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2512.p2525,GridMinus.atNode 2525,GridMinus.atNode 2526,NodeMinus39.w29,CompactMinus2512.checked2525,CompactMinus2512.small2525,CompactMinus2512.nodes2525,NodeMinus39.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2512.p2526,GridMinus.atNode 2526,GridMinus.atNode 2527,NodeMinus39.w30,CompactMinus2512.checked2526,CompactMinus2512.small2526,CompactMinus2512.nodes2526,NodeMinus39.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2512.p2527,GridMinus.atNode 2527,GridMinus.atNode 2528,NodeMinus39.w31,CompactMinus2512.checked2527,CompactMinus2512.small2527,CompactMinus2512.nodes2527,NodeMinus39.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2528.p2528,GridMinus.atNode 2528,GridMinus.atNode 2529,NodeMinus39.w32,CompactMinus2528.checked2528,CompactMinus2528.small2528,CompactMinus2528.nodes2528,NodeMinus39.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2528.p2529,GridMinus.atNode 2529,GridMinus.atNode 2530,NodeMinus39.w33,CompactMinus2528.checked2529,CompactMinus2528.small2529,CompactMinus2528.nodes2529,NodeMinus39.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2528.p2530,GridMinus.atNode 2530,GridMinus.atNode 2531,NodeMinus39.w34,CompactMinus2528.checked2530,CompactMinus2528.small2530,CompactMinus2528.nodes2530,NodeMinus39.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2528.p2531,GridMinus.atNode 2531,GridMinus.atNode 2532,NodeMinus39.w35,CompactMinus2528.checked2531,CompactMinus2528.small2531,CompactMinus2528.nodes2531,NodeMinus39.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2528.p2532,GridMinus.atNode 2532,GridMinus.atNode 2533,NodeMinus39.w36,CompactMinus2528.checked2532,CompactMinus2528.small2532,CompactMinus2528.nodes2532,NodeMinus39.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2528.p2533,GridMinus.atNode 2533,GridMinus.atNode 2534,NodeMinus39.w37,CompactMinus2528.checked2533,CompactMinus2528.small2533,CompactMinus2528.nodes2533,NodeMinus39.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2528.p2534,GridMinus.atNode 2534,GridMinus.atNode 2535,NodeMinus39.w38,CompactMinus2528.checked2534,CompactMinus2528.small2534,CompactMinus2528.nodes2534,NodeMinus39.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2528.p2535,GridMinus.atNode 2535,GridMinus.atNode 2536,NodeMinus39.w39,CompactMinus2528.checked2535,CompactMinus2528.small2535,CompactMinus2528.nodes2535,NodeMinus39.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2528.p2536,GridMinus.atNode 2536,GridMinus.atNode 2537,NodeMinus39.w40,CompactMinus2528.checked2536,CompactMinus2528.small2536,CompactMinus2528.nodes2536,NodeMinus39.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2528.p2537,GridMinus.atNode 2537,GridMinus.atNode 2538,NodeMinus39.w41,CompactMinus2528.checked2537,CompactMinus2528.small2537,CompactMinus2528.nodes2537,NodeMinus39.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2528.p2538,GridMinus.atNode 2538,GridMinus.atNode 2539,NodeMinus39.w42,CompactMinus2528.checked2538,CompactMinus2528.small2538,CompactMinus2528.nodes2538,NodeMinus39.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2528.p2539,GridMinus.atNode 2539,GridMinus.atNode 2540,NodeMinus39.w43,CompactMinus2528.checked2539,CompactMinus2528.small2539,CompactMinus2528.nodes2539,NodeMinus39.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2528.p2540,GridMinus.atNode 2540,GridMinus.atNode 2541,NodeMinus39.w44,CompactMinus2528.checked2540,CompactMinus2528.small2540,CompactMinus2528.nodes2540,NodeMinus39.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2528.p2541,GridMinus.atNode 2541,GridMinus.atNode 2542,NodeMinus39.w45,CompactMinus2528.checked2541,CompactMinus2528.small2541,CompactMinus2528.nodes2541,NodeMinus39.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2528.p2542,GridMinus.atNode 2542,GridMinus.atNode 2543,NodeMinus39.w46,CompactMinus2528.checked2542,CompactMinus2528.small2542,CompactMinus2528.nodes2542,NodeMinus39.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2528.p2543,GridMinus.atNode 2543,GridMinus.atNode 2544,NodeMinus39.w47,CompactMinus2528.checked2543,CompactMinus2528.small2543,CompactMinus2528.nodes2543,NodeMinus39.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2544.p2544,GridMinus.atNode 2544,GridMinus.atNode 2545,NodeMinus39.w48,CompactMinus2544.checked2544,CompactMinus2544.small2544,CompactMinus2544.nodes2544,NodeMinus39.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2544.p2545,GridMinus.atNode 2545,GridMinus.atNode 2546,NodeMinus39.w49,CompactMinus2544.checked2545,CompactMinus2544.small2545,CompactMinus2544.nodes2545,NodeMinus39.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2544.p2546,GridMinus.atNode 2546,GridMinus.atNode 2547,NodeMinus39.w50,CompactMinus2544.checked2546,CompactMinus2544.small2546,CompactMinus2544.nodes2546,NodeMinus39.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2544.p2547,GridMinus.atNode 2547,GridMinus.atNode 2548,NodeMinus39.w51,CompactMinus2544.checked2547,CompactMinus2544.small2547,CompactMinus2544.nodes2547,NodeMinus39.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2544.p2548,GridMinus.atNode 2548,GridMinus.atNode 2549,NodeMinus39.w52,CompactMinus2544.checked2548,CompactMinus2544.small2548,CompactMinus2544.nodes2548,NodeMinus39.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2544.p2549,GridMinus.atNode 2549,GridMinus.atNode 2550,NodeMinus39.w53,CompactMinus2544.checked2549,CompactMinus2544.small2549,CompactMinus2544.nodes2549,NodeMinus39.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2544.p2550,GridMinus.atNode 2550,GridMinus.atNode 2551,NodeMinus39.w54,CompactMinus2544.checked2550,CompactMinus2544.small2550,CompactMinus2544.nodes2550,NodeMinus39.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2544.p2551,GridMinus.atNode 2551,GridMinus.atNode 2552,NodeMinus39.w55,CompactMinus2544.checked2551,CompactMinus2544.small2551,CompactMinus2544.nodes2551,NodeMinus39.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2544.p2552,GridMinus.atNode 2552,GridMinus.atNode 2553,NodeMinus39.w56,CompactMinus2544.checked2552,CompactMinus2544.small2552,CompactMinus2544.nodes2552,NodeMinus39.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2544.p2553,GridMinus.atNode 2553,GridMinus.atNode 2554,NodeMinus39.w57,CompactMinus2544.checked2553,CompactMinus2544.small2553,CompactMinus2544.nodes2553,NodeMinus39.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2544.p2554,GridMinus.atNode 2554,GridMinus.atNode 2555,NodeMinus39.w58,CompactMinus2544.checked2554,CompactMinus2544.small2554,CompactMinus2544.nodes2554,NodeMinus39.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2544.p2555,GridMinus.atNode 2555,GridMinus.atNode 2556,NodeMinus39.w59,CompactMinus2544.checked2555,CompactMinus2544.small2555,CompactMinus2544.nodes2555,NodeMinus39.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2544.p2556,GridMinus.atNode 2556,GridMinus.atNode 2557,NodeMinus39.w60,CompactMinus2544.checked2556,CompactMinus2544.small2556,CompactMinus2544.nodes2556,NodeMinus39.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2544.p2557,GridMinus.atNode 2557,GridMinus.atNode 2558,NodeMinus39.w61,CompactMinus2544.checked2557,CompactMinus2544.small2557,CompactMinus2544.nodes2557,NodeMinus39.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2544.p2558,GridMinus.atNode 2558,GridMinus.atNode 2559,NodeMinus39.w62,CompactMinus2544.checked2558,CompactMinus2544.small2558,CompactMinus2544.nodes2558,NodeMinus39.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2544.p2559,GridMinus.atNode 2559,GridMinus.atNode 2560,NodeMinus39.w63,CompactMinus2544.checked2559,CompactMinus2544.small2559,CompactMinus2544.nodes2559,NodeMinus39.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (2496+j) ∧
    (atRow j).right=GridMinus.atNode (2496+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus39
