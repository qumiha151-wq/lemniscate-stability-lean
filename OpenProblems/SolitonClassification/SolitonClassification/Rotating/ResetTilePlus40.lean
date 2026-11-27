import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus2560
import SolitonClassification.Rotating.ResetPackedPlus2576
import SolitonClassification.Rotating.ResetPackedPlus2592
import SolitonClassification.Rotating.ResetPackedPlus2608
namespace SolitonClassification.Rotating.DyadicReset.TilePlus40
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus2560.p2560,GridPlus.atNode 2560,GridPlus.atNode 2561,NodePlus40.w0,CompactPlus2560.checked2560,CompactPlus2560.small2560,CompactPlus2560.nodes2560,NodePlus40.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus2560.p2561,GridPlus.atNode 2561,GridPlus.atNode 2562,NodePlus40.w1,CompactPlus2560.checked2561,CompactPlus2560.small2561,CompactPlus2560.nodes2561,NodePlus40.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus2560.p2562,GridPlus.atNode 2562,GridPlus.atNode 2563,NodePlus40.w2,CompactPlus2560.checked2562,CompactPlus2560.small2562,CompactPlus2560.nodes2562,NodePlus40.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus2560.p2563,GridPlus.atNode 2563,GridPlus.atNode 2564,NodePlus40.w3,CompactPlus2560.checked2563,CompactPlus2560.small2563,CompactPlus2560.nodes2563,NodePlus40.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus2560.p2564,GridPlus.atNode 2564,GridPlus.atNode 2565,NodePlus40.w4,CompactPlus2560.checked2564,CompactPlus2560.small2564,CompactPlus2560.nodes2564,NodePlus40.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus2560.p2565,GridPlus.atNode 2565,GridPlus.atNode 2566,NodePlus40.w5,CompactPlus2560.checked2565,CompactPlus2560.small2565,CompactPlus2560.nodes2565,NodePlus40.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus2560.p2566,GridPlus.atNode 2566,GridPlus.atNode 2567,NodePlus40.w6,CompactPlus2560.checked2566,CompactPlus2560.small2566,CompactPlus2560.nodes2566,NodePlus40.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus2560.p2567,GridPlus.atNode 2567,GridPlus.atNode 2568,NodePlus40.w7,CompactPlus2560.checked2567,CompactPlus2560.small2567,CompactPlus2560.nodes2567,NodePlus40.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus2560.p2568,GridPlus.atNode 2568,GridPlus.atNode 2569,NodePlus40.w8,CompactPlus2560.checked2568,CompactPlus2560.small2568,CompactPlus2560.nodes2568,NodePlus40.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus2560.p2569,GridPlus.atNode 2569,GridPlus.atNode 2570,NodePlus40.w9,CompactPlus2560.checked2569,CompactPlus2560.small2569,CompactPlus2560.nodes2569,NodePlus40.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus2560.p2570,GridPlus.atNode 2570,GridPlus.atNode 2571,NodePlus40.w10,CompactPlus2560.checked2570,CompactPlus2560.small2570,CompactPlus2560.nodes2570,NodePlus40.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus2560.p2571,GridPlus.atNode 2571,GridPlus.atNode 2572,NodePlus40.w11,CompactPlus2560.checked2571,CompactPlus2560.small2571,CompactPlus2560.nodes2571,NodePlus40.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus2560.p2572,GridPlus.atNode 2572,GridPlus.atNode 2573,NodePlus40.w12,CompactPlus2560.checked2572,CompactPlus2560.small2572,CompactPlus2560.nodes2572,NodePlus40.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus2560.p2573,GridPlus.atNode 2573,GridPlus.atNode 2574,NodePlus40.w13,CompactPlus2560.checked2573,CompactPlus2560.small2573,CompactPlus2560.nodes2573,NodePlus40.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus2560.p2574,GridPlus.atNode 2574,GridPlus.atNode 2575,NodePlus40.w14,CompactPlus2560.checked2574,CompactPlus2560.small2574,CompactPlus2560.nodes2574,NodePlus40.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus2560.p2575,GridPlus.atNode 2575,GridPlus.atNode 2576,NodePlus40.w15,CompactPlus2560.checked2575,CompactPlus2560.small2575,CompactPlus2560.nodes2575,NodePlus40.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus2576.p2576,GridPlus.atNode 2576,GridPlus.atNode 2577,NodePlus40.w16,CompactPlus2576.checked2576,CompactPlus2576.small2576,CompactPlus2576.nodes2576,NodePlus40.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus2576.p2577,GridPlus.atNode 2577,GridPlus.atNode 2578,NodePlus40.w17,CompactPlus2576.checked2577,CompactPlus2576.small2577,CompactPlus2576.nodes2577,NodePlus40.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus2576.p2578,GridPlus.atNode 2578,GridPlus.atNode 2579,NodePlus40.w18,CompactPlus2576.checked2578,CompactPlus2576.small2578,CompactPlus2576.nodes2578,NodePlus40.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus2576.p2579,GridPlus.atNode 2579,GridPlus.atNode 2580,NodePlus40.w19,CompactPlus2576.checked2579,CompactPlus2576.small2579,CompactPlus2576.nodes2579,NodePlus40.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus2576.p2580,GridPlus.atNode 2580,GridPlus.atNode 2581,NodePlus40.w20,CompactPlus2576.checked2580,CompactPlus2576.small2580,CompactPlus2576.nodes2580,NodePlus40.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus2576.p2581,GridPlus.atNode 2581,GridPlus.atNode 2582,NodePlus40.w21,CompactPlus2576.checked2581,CompactPlus2576.small2581,CompactPlus2576.nodes2581,NodePlus40.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus2576.p2582,GridPlus.atNode 2582,GridPlus.atNode 2583,NodePlus40.w22,CompactPlus2576.checked2582,CompactPlus2576.small2582,CompactPlus2576.nodes2582,NodePlus40.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus2576.p2583,GridPlus.atNode 2583,GridPlus.atNode 2584,NodePlus40.w23,CompactPlus2576.checked2583,CompactPlus2576.small2583,CompactPlus2576.nodes2583,NodePlus40.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus2576.p2584,GridPlus.atNode 2584,GridPlus.atNode 2585,NodePlus40.w24,CompactPlus2576.checked2584,CompactPlus2576.small2584,CompactPlus2576.nodes2584,NodePlus40.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus2576.p2585,GridPlus.atNode 2585,GridPlus.atNode 2586,NodePlus40.w25,CompactPlus2576.checked2585,CompactPlus2576.small2585,CompactPlus2576.nodes2585,NodePlus40.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus2576.p2586,GridPlus.atNode 2586,GridPlus.atNode 2587,NodePlus40.w26,CompactPlus2576.checked2586,CompactPlus2576.small2586,CompactPlus2576.nodes2586,NodePlus40.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus2576.p2587,GridPlus.atNode 2587,GridPlus.atNode 2588,NodePlus40.w27,CompactPlus2576.checked2587,CompactPlus2576.small2587,CompactPlus2576.nodes2587,NodePlus40.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus2576.p2588,GridPlus.atNode 2588,GridPlus.atNode 2589,NodePlus40.w28,CompactPlus2576.checked2588,CompactPlus2576.small2588,CompactPlus2576.nodes2588,NodePlus40.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus2576.p2589,GridPlus.atNode 2589,GridPlus.atNode 2590,NodePlus40.w29,CompactPlus2576.checked2589,CompactPlus2576.small2589,CompactPlus2576.nodes2589,NodePlus40.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus2576.p2590,GridPlus.atNode 2590,GridPlus.atNode 2591,NodePlus40.w30,CompactPlus2576.checked2590,CompactPlus2576.small2590,CompactPlus2576.nodes2590,NodePlus40.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus2576.p2591,GridPlus.atNode 2591,GridPlus.atNode 2592,NodePlus40.w31,CompactPlus2576.checked2591,CompactPlus2576.small2591,CompactPlus2576.nodes2591,NodePlus40.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus2592.p2592,GridPlus.atNode 2592,GridPlus.atNode 2593,NodePlus40.w32,CompactPlus2592.checked2592,CompactPlus2592.small2592,CompactPlus2592.nodes2592,NodePlus40.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus2592.p2593,GridPlus.atNode 2593,GridPlus.atNode 2594,NodePlus40.w33,CompactPlus2592.checked2593,CompactPlus2592.small2593,CompactPlus2592.nodes2593,NodePlus40.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus2592.p2594,GridPlus.atNode 2594,GridPlus.atNode 2595,NodePlus40.w34,CompactPlus2592.checked2594,CompactPlus2592.small2594,CompactPlus2592.nodes2594,NodePlus40.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus2592.p2595,GridPlus.atNode 2595,GridPlus.atNode 2596,NodePlus40.w35,CompactPlus2592.checked2595,CompactPlus2592.small2595,CompactPlus2592.nodes2595,NodePlus40.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus2592.p2596,GridPlus.atNode 2596,GridPlus.atNode 2597,NodePlus40.w36,CompactPlus2592.checked2596,CompactPlus2592.small2596,CompactPlus2592.nodes2596,NodePlus40.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus2592.p2597,GridPlus.atNode 2597,GridPlus.atNode 2598,NodePlus40.w37,CompactPlus2592.checked2597,CompactPlus2592.small2597,CompactPlus2592.nodes2597,NodePlus40.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus2592.p2598,GridPlus.atNode 2598,GridPlus.atNode 2599,NodePlus40.w38,CompactPlus2592.checked2598,CompactPlus2592.small2598,CompactPlus2592.nodes2598,NodePlus40.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus2592.p2599,GridPlus.atNode 2599,GridPlus.atNode 2600,NodePlus40.w39,CompactPlus2592.checked2599,CompactPlus2592.small2599,CompactPlus2592.nodes2599,NodePlus40.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus2592.p2600,GridPlus.atNode 2600,GridPlus.atNode 2601,NodePlus40.w40,CompactPlus2592.checked2600,CompactPlus2592.small2600,CompactPlus2592.nodes2600,NodePlus40.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus2592.p2601,GridPlus.atNode 2601,GridPlus.atNode 2602,NodePlus40.w41,CompactPlus2592.checked2601,CompactPlus2592.small2601,CompactPlus2592.nodes2601,NodePlus40.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus2592.p2602,GridPlus.atNode 2602,GridPlus.atNode 2603,NodePlus40.w42,CompactPlus2592.checked2602,CompactPlus2592.small2602,CompactPlus2592.nodes2602,NodePlus40.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus2592.p2603,GridPlus.atNode 2603,GridPlus.atNode 2604,NodePlus40.w43,CompactPlus2592.checked2603,CompactPlus2592.small2603,CompactPlus2592.nodes2603,NodePlus40.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus2592.p2604,GridPlus.atNode 2604,GridPlus.atNode 2605,NodePlus40.w44,CompactPlus2592.checked2604,CompactPlus2592.small2604,CompactPlus2592.nodes2604,NodePlus40.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus2592.p2605,GridPlus.atNode 2605,GridPlus.atNode 2606,NodePlus40.w45,CompactPlus2592.checked2605,CompactPlus2592.small2605,CompactPlus2592.nodes2605,NodePlus40.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus2592.p2606,GridPlus.atNode 2606,GridPlus.atNode 2607,NodePlus40.w46,CompactPlus2592.checked2606,CompactPlus2592.small2606,CompactPlus2592.nodes2606,NodePlus40.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus2592.p2607,GridPlus.atNode 2607,GridPlus.atNode 2608,NodePlus40.w47,CompactPlus2592.checked2607,CompactPlus2592.small2607,CompactPlus2592.nodes2607,NodePlus40.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus2608.p2608,GridPlus.atNode 2608,GridPlus.atNode 2609,NodePlus40.w48,CompactPlus2608.checked2608,CompactPlus2608.small2608,CompactPlus2608.nodes2608,NodePlus40.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus2608.p2609,GridPlus.atNode 2609,GridPlus.atNode 2610,NodePlus40.w49,CompactPlus2608.checked2609,CompactPlus2608.small2609,CompactPlus2608.nodes2609,NodePlus40.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus2608.p2610,GridPlus.atNode 2610,GridPlus.atNode 2611,NodePlus40.w50,CompactPlus2608.checked2610,CompactPlus2608.small2610,CompactPlus2608.nodes2610,NodePlus40.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus2608.p2611,GridPlus.atNode 2611,GridPlus.atNode 2612,NodePlus40.w51,CompactPlus2608.checked2611,CompactPlus2608.small2611,CompactPlus2608.nodes2611,NodePlus40.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus2608.p2612,GridPlus.atNode 2612,GridPlus.atNode 2613,NodePlus40.w52,CompactPlus2608.checked2612,CompactPlus2608.small2612,CompactPlus2608.nodes2612,NodePlus40.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus2608.p2613,GridPlus.atNode 2613,GridPlus.atNode 2614,NodePlus40.w53,CompactPlus2608.checked2613,CompactPlus2608.small2613,CompactPlus2608.nodes2613,NodePlus40.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus2608.p2614,GridPlus.atNode 2614,GridPlus.atNode 2615,NodePlus40.w54,CompactPlus2608.checked2614,CompactPlus2608.small2614,CompactPlus2608.nodes2614,NodePlus40.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus2608.p2615,GridPlus.atNode 2615,GridPlus.atNode 2616,NodePlus40.w55,CompactPlus2608.checked2615,CompactPlus2608.small2615,CompactPlus2608.nodes2615,NodePlus40.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus2608.p2616,GridPlus.atNode 2616,GridPlus.atNode 2617,NodePlus40.w56,CompactPlus2608.checked2616,CompactPlus2608.small2616,CompactPlus2608.nodes2616,NodePlus40.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus2608.p2617,GridPlus.atNode 2617,GridPlus.atNode 2618,NodePlus40.w57,CompactPlus2608.checked2617,CompactPlus2608.small2617,CompactPlus2608.nodes2617,NodePlus40.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus2608.p2618,GridPlus.atNode 2618,GridPlus.atNode 2619,NodePlus40.w58,CompactPlus2608.checked2618,CompactPlus2608.small2618,CompactPlus2608.nodes2618,NodePlus40.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus2608.p2619,GridPlus.atNode 2619,GridPlus.atNode 2620,NodePlus40.w59,CompactPlus2608.checked2619,CompactPlus2608.small2619,CompactPlus2608.nodes2619,NodePlus40.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus2608.p2620,GridPlus.atNode 2620,GridPlus.atNode 2621,NodePlus40.w60,CompactPlus2608.checked2620,CompactPlus2608.small2620,CompactPlus2608.nodes2620,NodePlus40.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus2608.p2621,GridPlus.atNode 2621,GridPlus.atNode 2622,NodePlus40.w61,CompactPlus2608.checked2621,CompactPlus2608.small2621,CompactPlus2608.nodes2621,NodePlus40.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus2608.p2622,GridPlus.atNode 2622,GridPlus.atNode 2623,NodePlus40.w62,CompactPlus2608.checked2622,CompactPlus2608.small2622,CompactPlus2608.nodes2622,NodePlus40.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus2608.p2623,GridPlus.atNode 2623,GridPlus.atNode 2624,NodePlus40.w63,CompactPlus2608.checked2623,CompactPlus2608.small2623,CompactPlus2608.nodes2623,NodePlus40.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (2560+j) ∧
    (atRow j).right=GridPlus.atNode (2560+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus40
