import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus2496
import SolitonClassification.Rotating.ResetPackedPlus2512
import SolitonClassification.Rotating.ResetPackedPlus2528
import SolitonClassification.Rotating.ResetPackedPlus2544
namespace SolitonClassification.Rotating.DyadicReset.TilePlus39
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus2496.p2496,GridPlus.atNode 2496,GridPlus.atNode 2497,NodePlus39.w0,CompactPlus2496.checked2496,CompactPlus2496.small2496,CompactPlus2496.nodes2496,NodePlus39.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus2496.p2497,GridPlus.atNode 2497,GridPlus.atNode 2498,NodePlus39.w1,CompactPlus2496.checked2497,CompactPlus2496.small2497,CompactPlus2496.nodes2497,NodePlus39.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus2496.p2498,GridPlus.atNode 2498,GridPlus.atNode 2499,NodePlus39.w2,CompactPlus2496.checked2498,CompactPlus2496.small2498,CompactPlus2496.nodes2498,NodePlus39.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus2496.p2499,GridPlus.atNode 2499,GridPlus.atNode 2500,NodePlus39.w3,CompactPlus2496.checked2499,CompactPlus2496.small2499,CompactPlus2496.nodes2499,NodePlus39.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus2496.p2500,GridPlus.atNode 2500,GridPlus.atNode 2501,NodePlus39.w4,CompactPlus2496.checked2500,CompactPlus2496.small2500,CompactPlus2496.nodes2500,NodePlus39.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus2496.p2501,GridPlus.atNode 2501,GridPlus.atNode 2502,NodePlus39.w5,CompactPlus2496.checked2501,CompactPlus2496.small2501,CompactPlus2496.nodes2501,NodePlus39.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus2496.p2502,GridPlus.atNode 2502,GridPlus.atNode 2503,NodePlus39.w6,CompactPlus2496.checked2502,CompactPlus2496.small2502,CompactPlus2496.nodes2502,NodePlus39.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus2496.p2503,GridPlus.atNode 2503,GridPlus.atNode 2504,NodePlus39.w7,CompactPlus2496.checked2503,CompactPlus2496.small2503,CompactPlus2496.nodes2503,NodePlus39.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus2496.p2504,GridPlus.atNode 2504,GridPlus.atNode 2505,NodePlus39.w8,CompactPlus2496.checked2504,CompactPlus2496.small2504,CompactPlus2496.nodes2504,NodePlus39.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus2496.p2505,GridPlus.atNode 2505,GridPlus.atNode 2506,NodePlus39.w9,CompactPlus2496.checked2505,CompactPlus2496.small2505,CompactPlus2496.nodes2505,NodePlus39.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus2496.p2506,GridPlus.atNode 2506,GridPlus.atNode 2507,NodePlus39.w10,CompactPlus2496.checked2506,CompactPlus2496.small2506,CompactPlus2496.nodes2506,NodePlus39.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus2496.p2507,GridPlus.atNode 2507,GridPlus.atNode 2508,NodePlus39.w11,CompactPlus2496.checked2507,CompactPlus2496.small2507,CompactPlus2496.nodes2507,NodePlus39.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus2496.p2508,GridPlus.atNode 2508,GridPlus.atNode 2509,NodePlus39.w12,CompactPlus2496.checked2508,CompactPlus2496.small2508,CompactPlus2496.nodes2508,NodePlus39.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus2496.p2509,GridPlus.atNode 2509,GridPlus.atNode 2510,NodePlus39.w13,CompactPlus2496.checked2509,CompactPlus2496.small2509,CompactPlus2496.nodes2509,NodePlus39.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus2496.p2510,GridPlus.atNode 2510,GridPlus.atNode 2511,NodePlus39.w14,CompactPlus2496.checked2510,CompactPlus2496.small2510,CompactPlus2496.nodes2510,NodePlus39.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus2496.p2511,GridPlus.atNode 2511,GridPlus.atNode 2512,NodePlus39.w15,CompactPlus2496.checked2511,CompactPlus2496.small2511,CompactPlus2496.nodes2511,NodePlus39.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus2512.p2512,GridPlus.atNode 2512,GridPlus.atNode 2513,NodePlus39.w16,CompactPlus2512.checked2512,CompactPlus2512.small2512,CompactPlus2512.nodes2512,NodePlus39.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus2512.p2513,GridPlus.atNode 2513,GridPlus.atNode 2514,NodePlus39.w17,CompactPlus2512.checked2513,CompactPlus2512.small2513,CompactPlus2512.nodes2513,NodePlus39.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus2512.p2514,GridPlus.atNode 2514,GridPlus.atNode 2515,NodePlus39.w18,CompactPlus2512.checked2514,CompactPlus2512.small2514,CompactPlus2512.nodes2514,NodePlus39.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus2512.p2515,GridPlus.atNode 2515,GridPlus.atNode 2516,NodePlus39.w19,CompactPlus2512.checked2515,CompactPlus2512.small2515,CompactPlus2512.nodes2515,NodePlus39.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus2512.p2516,GridPlus.atNode 2516,GridPlus.atNode 2517,NodePlus39.w20,CompactPlus2512.checked2516,CompactPlus2512.small2516,CompactPlus2512.nodes2516,NodePlus39.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus2512.p2517,GridPlus.atNode 2517,GridPlus.atNode 2518,NodePlus39.w21,CompactPlus2512.checked2517,CompactPlus2512.small2517,CompactPlus2512.nodes2517,NodePlus39.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus2512.p2518,GridPlus.atNode 2518,GridPlus.atNode 2519,NodePlus39.w22,CompactPlus2512.checked2518,CompactPlus2512.small2518,CompactPlus2512.nodes2518,NodePlus39.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus2512.p2519,GridPlus.atNode 2519,GridPlus.atNode 2520,NodePlus39.w23,CompactPlus2512.checked2519,CompactPlus2512.small2519,CompactPlus2512.nodes2519,NodePlus39.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus2512.p2520,GridPlus.atNode 2520,GridPlus.atNode 2521,NodePlus39.w24,CompactPlus2512.checked2520,CompactPlus2512.small2520,CompactPlus2512.nodes2520,NodePlus39.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus2512.p2521,GridPlus.atNode 2521,GridPlus.atNode 2522,NodePlus39.w25,CompactPlus2512.checked2521,CompactPlus2512.small2521,CompactPlus2512.nodes2521,NodePlus39.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus2512.p2522,GridPlus.atNode 2522,GridPlus.atNode 2523,NodePlus39.w26,CompactPlus2512.checked2522,CompactPlus2512.small2522,CompactPlus2512.nodes2522,NodePlus39.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus2512.p2523,GridPlus.atNode 2523,GridPlus.atNode 2524,NodePlus39.w27,CompactPlus2512.checked2523,CompactPlus2512.small2523,CompactPlus2512.nodes2523,NodePlus39.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus2512.p2524,GridPlus.atNode 2524,GridPlus.atNode 2525,NodePlus39.w28,CompactPlus2512.checked2524,CompactPlus2512.small2524,CompactPlus2512.nodes2524,NodePlus39.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus2512.p2525,GridPlus.atNode 2525,GridPlus.atNode 2526,NodePlus39.w29,CompactPlus2512.checked2525,CompactPlus2512.small2525,CompactPlus2512.nodes2525,NodePlus39.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus2512.p2526,GridPlus.atNode 2526,GridPlus.atNode 2527,NodePlus39.w30,CompactPlus2512.checked2526,CompactPlus2512.small2526,CompactPlus2512.nodes2526,NodePlus39.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus2512.p2527,GridPlus.atNode 2527,GridPlus.atNode 2528,NodePlus39.w31,CompactPlus2512.checked2527,CompactPlus2512.small2527,CompactPlus2512.nodes2527,NodePlus39.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus2528.p2528,GridPlus.atNode 2528,GridPlus.atNode 2529,NodePlus39.w32,CompactPlus2528.checked2528,CompactPlus2528.small2528,CompactPlus2528.nodes2528,NodePlus39.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus2528.p2529,GridPlus.atNode 2529,GridPlus.atNode 2530,NodePlus39.w33,CompactPlus2528.checked2529,CompactPlus2528.small2529,CompactPlus2528.nodes2529,NodePlus39.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus2528.p2530,GridPlus.atNode 2530,GridPlus.atNode 2531,NodePlus39.w34,CompactPlus2528.checked2530,CompactPlus2528.small2530,CompactPlus2528.nodes2530,NodePlus39.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus2528.p2531,GridPlus.atNode 2531,GridPlus.atNode 2532,NodePlus39.w35,CompactPlus2528.checked2531,CompactPlus2528.small2531,CompactPlus2528.nodes2531,NodePlus39.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus2528.p2532,GridPlus.atNode 2532,GridPlus.atNode 2533,NodePlus39.w36,CompactPlus2528.checked2532,CompactPlus2528.small2532,CompactPlus2528.nodes2532,NodePlus39.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus2528.p2533,GridPlus.atNode 2533,GridPlus.atNode 2534,NodePlus39.w37,CompactPlus2528.checked2533,CompactPlus2528.small2533,CompactPlus2528.nodes2533,NodePlus39.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus2528.p2534,GridPlus.atNode 2534,GridPlus.atNode 2535,NodePlus39.w38,CompactPlus2528.checked2534,CompactPlus2528.small2534,CompactPlus2528.nodes2534,NodePlus39.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus2528.p2535,GridPlus.atNode 2535,GridPlus.atNode 2536,NodePlus39.w39,CompactPlus2528.checked2535,CompactPlus2528.small2535,CompactPlus2528.nodes2535,NodePlus39.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus2528.p2536,GridPlus.atNode 2536,GridPlus.atNode 2537,NodePlus39.w40,CompactPlus2528.checked2536,CompactPlus2528.small2536,CompactPlus2528.nodes2536,NodePlus39.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus2528.p2537,GridPlus.atNode 2537,GridPlus.atNode 2538,NodePlus39.w41,CompactPlus2528.checked2537,CompactPlus2528.small2537,CompactPlus2528.nodes2537,NodePlus39.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus2528.p2538,GridPlus.atNode 2538,GridPlus.atNode 2539,NodePlus39.w42,CompactPlus2528.checked2538,CompactPlus2528.small2538,CompactPlus2528.nodes2538,NodePlus39.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus2528.p2539,GridPlus.atNode 2539,GridPlus.atNode 2540,NodePlus39.w43,CompactPlus2528.checked2539,CompactPlus2528.small2539,CompactPlus2528.nodes2539,NodePlus39.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus2528.p2540,GridPlus.atNode 2540,GridPlus.atNode 2541,NodePlus39.w44,CompactPlus2528.checked2540,CompactPlus2528.small2540,CompactPlus2528.nodes2540,NodePlus39.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus2528.p2541,GridPlus.atNode 2541,GridPlus.atNode 2542,NodePlus39.w45,CompactPlus2528.checked2541,CompactPlus2528.small2541,CompactPlus2528.nodes2541,NodePlus39.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus2528.p2542,GridPlus.atNode 2542,GridPlus.atNode 2543,NodePlus39.w46,CompactPlus2528.checked2542,CompactPlus2528.small2542,CompactPlus2528.nodes2542,NodePlus39.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus2528.p2543,GridPlus.atNode 2543,GridPlus.atNode 2544,NodePlus39.w47,CompactPlus2528.checked2543,CompactPlus2528.small2543,CompactPlus2528.nodes2543,NodePlus39.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus2544.p2544,GridPlus.atNode 2544,GridPlus.atNode 2545,NodePlus39.w48,CompactPlus2544.checked2544,CompactPlus2544.small2544,CompactPlus2544.nodes2544,NodePlus39.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus2544.p2545,GridPlus.atNode 2545,GridPlus.atNode 2546,NodePlus39.w49,CompactPlus2544.checked2545,CompactPlus2544.small2545,CompactPlus2544.nodes2545,NodePlus39.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus2544.p2546,GridPlus.atNode 2546,GridPlus.atNode 2547,NodePlus39.w50,CompactPlus2544.checked2546,CompactPlus2544.small2546,CompactPlus2544.nodes2546,NodePlus39.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus2544.p2547,GridPlus.atNode 2547,GridPlus.atNode 2548,NodePlus39.w51,CompactPlus2544.checked2547,CompactPlus2544.small2547,CompactPlus2544.nodes2547,NodePlus39.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus2544.p2548,GridPlus.atNode 2548,GridPlus.atNode 2549,NodePlus39.w52,CompactPlus2544.checked2548,CompactPlus2544.small2548,CompactPlus2544.nodes2548,NodePlus39.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus2544.p2549,GridPlus.atNode 2549,GridPlus.atNode 2550,NodePlus39.w53,CompactPlus2544.checked2549,CompactPlus2544.small2549,CompactPlus2544.nodes2549,NodePlus39.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus2544.p2550,GridPlus.atNode 2550,GridPlus.atNode 2551,NodePlus39.w54,CompactPlus2544.checked2550,CompactPlus2544.small2550,CompactPlus2544.nodes2550,NodePlus39.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus2544.p2551,GridPlus.atNode 2551,GridPlus.atNode 2552,NodePlus39.w55,CompactPlus2544.checked2551,CompactPlus2544.small2551,CompactPlus2544.nodes2551,NodePlus39.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus2544.p2552,GridPlus.atNode 2552,GridPlus.atNode 2553,NodePlus39.w56,CompactPlus2544.checked2552,CompactPlus2544.small2552,CompactPlus2544.nodes2552,NodePlus39.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus2544.p2553,GridPlus.atNode 2553,GridPlus.atNode 2554,NodePlus39.w57,CompactPlus2544.checked2553,CompactPlus2544.small2553,CompactPlus2544.nodes2553,NodePlus39.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus2544.p2554,GridPlus.atNode 2554,GridPlus.atNode 2555,NodePlus39.w58,CompactPlus2544.checked2554,CompactPlus2544.small2554,CompactPlus2544.nodes2554,NodePlus39.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus2544.p2555,GridPlus.atNode 2555,GridPlus.atNode 2556,NodePlus39.w59,CompactPlus2544.checked2555,CompactPlus2544.small2555,CompactPlus2544.nodes2555,NodePlus39.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus2544.p2556,GridPlus.atNode 2556,GridPlus.atNode 2557,NodePlus39.w60,CompactPlus2544.checked2556,CompactPlus2544.small2556,CompactPlus2544.nodes2556,NodePlus39.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus2544.p2557,GridPlus.atNode 2557,GridPlus.atNode 2558,NodePlus39.w61,CompactPlus2544.checked2557,CompactPlus2544.small2557,CompactPlus2544.nodes2557,NodePlus39.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus2544.p2558,GridPlus.atNode 2558,GridPlus.atNode 2559,NodePlus39.w62,CompactPlus2544.checked2558,CompactPlus2544.small2558,CompactPlus2544.nodes2558,NodePlus39.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus2544.p2559,GridPlus.atNode 2559,GridPlus.atNode 2560,NodePlus39.w63,CompactPlus2544.checked2559,CompactPlus2544.small2559,CompactPlus2544.nodes2559,NodePlus39.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (2496+j) ∧
    (atRow j).right=GridPlus.atNode (2496+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus39
