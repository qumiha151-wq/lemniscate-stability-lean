import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus2560
import SolitonClassification.Rotating.ResetPackedMinus2576
import SolitonClassification.Rotating.ResetPackedMinus2592
import SolitonClassification.Rotating.ResetPackedMinus2608
namespace SolitonClassification.Rotating.DyadicReset.TileMinus40
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2560.p2560,GridMinus.atNode 2560,GridMinus.atNode 2561,NodeMinus40.w0,CompactMinus2560.checked2560,CompactMinus2560.small2560,CompactMinus2560.nodes2560,NodeMinus40.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2560.p2561,GridMinus.atNode 2561,GridMinus.atNode 2562,NodeMinus40.w1,CompactMinus2560.checked2561,CompactMinus2560.small2561,CompactMinus2560.nodes2561,NodeMinus40.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2560.p2562,GridMinus.atNode 2562,GridMinus.atNode 2563,NodeMinus40.w2,CompactMinus2560.checked2562,CompactMinus2560.small2562,CompactMinus2560.nodes2562,NodeMinus40.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2560.p2563,GridMinus.atNode 2563,GridMinus.atNode 2564,NodeMinus40.w3,CompactMinus2560.checked2563,CompactMinus2560.small2563,CompactMinus2560.nodes2563,NodeMinus40.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2560.p2564,GridMinus.atNode 2564,GridMinus.atNode 2565,NodeMinus40.w4,CompactMinus2560.checked2564,CompactMinus2560.small2564,CompactMinus2560.nodes2564,NodeMinus40.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2560.p2565,GridMinus.atNode 2565,GridMinus.atNode 2566,NodeMinus40.w5,CompactMinus2560.checked2565,CompactMinus2560.small2565,CompactMinus2560.nodes2565,NodeMinus40.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2560.p2566,GridMinus.atNode 2566,GridMinus.atNode 2567,NodeMinus40.w6,CompactMinus2560.checked2566,CompactMinus2560.small2566,CompactMinus2560.nodes2566,NodeMinus40.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2560.p2567,GridMinus.atNode 2567,GridMinus.atNode 2568,NodeMinus40.w7,CompactMinus2560.checked2567,CompactMinus2560.small2567,CompactMinus2560.nodes2567,NodeMinus40.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2560.p2568,GridMinus.atNode 2568,GridMinus.atNode 2569,NodeMinus40.w8,CompactMinus2560.checked2568,CompactMinus2560.small2568,CompactMinus2560.nodes2568,NodeMinus40.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2560.p2569,GridMinus.atNode 2569,GridMinus.atNode 2570,NodeMinus40.w9,CompactMinus2560.checked2569,CompactMinus2560.small2569,CompactMinus2560.nodes2569,NodeMinus40.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2560.p2570,GridMinus.atNode 2570,GridMinus.atNode 2571,NodeMinus40.w10,CompactMinus2560.checked2570,CompactMinus2560.small2570,CompactMinus2560.nodes2570,NodeMinus40.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2560.p2571,GridMinus.atNode 2571,GridMinus.atNode 2572,NodeMinus40.w11,CompactMinus2560.checked2571,CompactMinus2560.small2571,CompactMinus2560.nodes2571,NodeMinus40.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2560.p2572,GridMinus.atNode 2572,GridMinus.atNode 2573,NodeMinus40.w12,CompactMinus2560.checked2572,CompactMinus2560.small2572,CompactMinus2560.nodes2572,NodeMinus40.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2560.p2573,GridMinus.atNode 2573,GridMinus.atNode 2574,NodeMinus40.w13,CompactMinus2560.checked2573,CompactMinus2560.small2573,CompactMinus2560.nodes2573,NodeMinus40.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2560.p2574,GridMinus.atNode 2574,GridMinus.atNode 2575,NodeMinus40.w14,CompactMinus2560.checked2574,CompactMinus2560.small2574,CompactMinus2560.nodes2574,NodeMinus40.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2560.p2575,GridMinus.atNode 2575,GridMinus.atNode 2576,NodeMinus40.w15,CompactMinus2560.checked2575,CompactMinus2560.small2575,CompactMinus2560.nodes2575,NodeMinus40.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2576.p2576,GridMinus.atNode 2576,GridMinus.atNode 2577,NodeMinus40.w16,CompactMinus2576.checked2576,CompactMinus2576.small2576,CompactMinus2576.nodes2576,NodeMinus40.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2576.p2577,GridMinus.atNode 2577,GridMinus.atNode 2578,NodeMinus40.w17,CompactMinus2576.checked2577,CompactMinus2576.small2577,CompactMinus2576.nodes2577,NodeMinus40.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2576.p2578,GridMinus.atNode 2578,GridMinus.atNode 2579,NodeMinus40.w18,CompactMinus2576.checked2578,CompactMinus2576.small2578,CompactMinus2576.nodes2578,NodeMinus40.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2576.p2579,GridMinus.atNode 2579,GridMinus.atNode 2580,NodeMinus40.w19,CompactMinus2576.checked2579,CompactMinus2576.small2579,CompactMinus2576.nodes2579,NodeMinus40.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2576.p2580,GridMinus.atNode 2580,GridMinus.atNode 2581,NodeMinus40.w20,CompactMinus2576.checked2580,CompactMinus2576.small2580,CompactMinus2576.nodes2580,NodeMinus40.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2576.p2581,GridMinus.atNode 2581,GridMinus.atNode 2582,NodeMinus40.w21,CompactMinus2576.checked2581,CompactMinus2576.small2581,CompactMinus2576.nodes2581,NodeMinus40.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2576.p2582,GridMinus.atNode 2582,GridMinus.atNode 2583,NodeMinus40.w22,CompactMinus2576.checked2582,CompactMinus2576.small2582,CompactMinus2576.nodes2582,NodeMinus40.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2576.p2583,GridMinus.atNode 2583,GridMinus.atNode 2584,NodeMinus40.w23,CompactMinus2576.checked2583,CompactMinus2576.small2583,CompactMinus2576.nodes2583,NodeMinus40.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2576.p2584,GridMinus.atNode 2584,GridMinus.atNode 2585,NodeMinus40.w24,CompactMinus2576.checked2584,CompactMinus2576.small2584,CompactMinus2576.nodes2584,NodeMinus40.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2576.p2585,GridMinus.atNode 2585,GridMinus.atNode 2586,NodeMinus40.w25,CompactMinus2576.checked2585,CompactMinus2576.small2585,CompactMinus2576.nodes2585,NodeMinus40.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2576.p2586,GridMinus.atNode 2586,GridMinus.atNode 2587,NodeMinus40.w26,CompactMinus2576.checked2586,CompactMinus2576.small2586,CompactMinus2576.nodes2586,NodeMinus40.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2576.p2587,GridMinus.atNode 2587,GridMinus.atNode 2588,NodeMinus40.w27,CompactMinus2576.checked2587,CompactMinus2576.small2587,CompactMinus2576.nodes2587,NodeMinus40.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2576.p2588,GridMinus.atNode 2588,GridMinus.atNode 2589,NodeMinus40.w28,CompactMinus2576.checked2588,CompactMinus2576.small2588,CompactMinus2576.nodes2588,NodeMinus40.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2576.p2589,GridMinus.atNode 2589,GridMinus.atNode 2590,NodeMinus40.w29,CompactMinus2576.checked2589,CompactMinus2576.small2589,CompactMinus2576.nodes2589,NodeMinus40.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2576.p2590,GridMinus.atNode 2590,GridMinus.atNode 2591,NodeMinus40.w30,CompactMinus2576.checked2590,CompactMinus2576.small2590,CompactMinus2576.nodes2590,NodeMinus40.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2576.p2591,GridMinus.atNode 2591,GridMinus.atNode 2592,NodeMinus40.w31,CompactMinus2576.checked2591,CompactMinus2576.small2591,CompactMinus2576.nodes2591,NodeMinus40.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2592.p2592,GridMinus.atNode 2592,GridMinus.atNode 2593,NodeMinus40.w32,CompactMinus2592.checked2592,CompactMinus2592.small2592,CompactMinus2592.nodes2592,NodeMinus40.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2592.p2593,GridMinus.atNode 2593,GridMinus.atNode 2594,NodeMinus40.w33,CompactMinus2592.checked2593,CompactMinus2592.small2593,CompactMinus2592.nodes2593,NodeMinus40.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2592.p2594,GridMinus.atNode 2594,GridMinus.atNode 2595,NodeMinus40.w34,CompactMinus2592.checked2594,CompactMinus2592.small2594,CompactMinus2592.nodes2594,NodeMinus40.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2592.p2595,GridMinus.atNode 2595,GridMinus.atNode 2596,NodeMinus40.w35,CompactMinus2592.checked2595,CompactMinus2592.small2595,CompactMinus2592.nodes2595,NodeMinus40.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2592.p2596,GridMinus.atNode 2596,GridMinus.atNode 2597,NodeMinus40.w36,CompactMinus2592.checked2596,CompactMinus2592.small2596,CompactMinus2592.nodes2596,NodeMinus40.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2592.p2597,GridMinus.atNode 2597,GridMinus.atNode 2598,NodeMinus40.w37,CompactMinus2592.checked2597,CompactMinus2592.small2597,CompactMinus2592.nodes2597,NodeMinus40.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2592.p2598,GridMinus.atNode 2598,GridMinus.atNode 2599,NodeMinus40.w38,CompactMinus2592.checked2598,CompactMinus2592.small2598,CompactMinus2592.nodes2598,NodeMinus40.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2592.p2599,GridMinus.atNode 2599,GridMinus.atNode 2600,NodeMinus40.w39,CompactMinus2592.checked2599,CompactMinus2592.small2599,CompactMinus2592.nodes2599,NodeMinus40.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2592.p2600,GridMinus.atNode 2600,GridMinus.atNode 2601,NodeMinus40.w40,CompactMinus2592.checked2600,CompactMinus2592.small2600,CompactMinus2592.nodes2600,NodeMinus40.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2592.p2601,GridMinus.atNode 2601,GridMinus.atNode 2602,NodeMinus40.w41,CompactMinus2592.checked2601,CompactMinus2592.small2601,CompactMinus2592.nodes2601,NodeMinus40.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2592.p2602,GridMinus.atNode 2602,GridMinus.atNode 2603,NodeMinus40.w42,CompactMinus2592.checked2602,CompactMinus2592.small2602,CompactMinus2592.nodes2602,NodeMinus40.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2592.p2603,GridMinus.atNode 2603,GridMinus.atNode 2604,NodeMinus40.w43,CompactMinus2592.checked2603,CompactMinus2592.small2603,CompactMinus2592.nodes2603,NodeMinus40.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2592.p2604,GridMinus.atNode 2604,GridMinus.atNode 2605,NodeMinus40.w44,CompactMinus2592.checked2604,CompactMinus2592.small2604,CompactMinus2592.nodes2604,NodeMinus40.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2592.p2605,GridMinus.atNode 2605,GridMinus.atNode 2606,NodeMinus40.w45,CompactMinus2592.checked2605,CompactMinus2592.small2605,CompactMinus2592.nodes2605,NodeMinus40.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2592.p2606,GridMinus.atNode 2606,GridMinus.atNode 2607,NodeMinus40.w46,CompactMinus2592.checked2606,CompactMinus2592.small2606,CompactMinus2592.nodes2606,NodeMinus40.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2592.p2607,GridMinus.atNode 2607,GridMinus.atNode 2608,NodeMinus40.w47,CompactMinus2592.checked2607,CompactMinus2592.small2607,CompactMinus2592.nodes2607,NodeMinus40.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2608.p2608,GridMinus.atNode 2608,GridMinus.atNode 2609,NodeMinus40.w48,CompactMinus2608.checked2608,CompactMinus2608.small2608,CompactMinus2608.nodes2608,NodeMinus40.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2608.p2609,GridMinus.atNode 2609,GridMinus.atNode 2610,NodeMinus40.w49,CompactMinus2608.checked2609,CompactMinus2608.small2609,CompactMinus2608.nodes2609,NodeMinus40.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2608.p2610,GridMinus.atNode 2610,GridMinus.atNode 2611,NodeMinus40.w50,CompactMinus2608.checked2610,CompactMinus2608.small2610,CompactMinus2608.nodes2610,NodeMinus40.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2608.p2611,GridMinus.atNode 2611,GridMinus.atNode 2612,NodeMinus40.w51,CompactMinus2608.checked2611,CompactMinus2608.small2611,CompactMinus2608.nodes2611,NodeMinus40.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2608.p2612,GridMinus.atNode 2612,GridMinus.atNode 2613,NodeMinus40.w52,CompactMinus2608.checked2612,CompactMinus2608.small2612,CompactMinus2608.nodes2612,NodeMinus40.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2608.p2613,GridMinus.atNode 2613,GridMinus.atNode 2614,NodeMinus40.w53,CompactMinus2608.checked2613,CompactMinus2608.small2613,CompactMinus2608.nodes2613,NodeMinus40.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2608.p2614,GridMinus.atNode 2614,GridMinus.atNode 2615,NodeMinus40.w54,CompactMinus2608.checked2614,CompactMinus2608.small2614,CompactMinus2608.nodes2614,NodeMinus40.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2608.p2615,GridMinus.atNode 2615,GridMinus.atNode 2616,NodeMinus40.w55,CompactMinus2608.checked2615,CompactMinus2608.small2615,CompactMinus2608.nodes2615,NodeMinus40.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2608.p2616,GridMinus.atNode 2616,GridMinus.atNode 2617,NodeMinus40.w56,CompactMinus2608.checked2616,CompactMinus2608.small2616,CompactMinus2608.nodes2616,NodeMinus40.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2608.p2617,GridMinus.atNode 2617,GridMinus.atNode 2618,NodeMinus40.w57,CompactMinus2608.checked2617,CompactMinus2608.small2617,CompactMinus2608.nodes2617,NodeMinus40.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2608.p2618,GridMinus.atNode 2618,GridMinus.atNode 2619,NodeMinus40.w58,CompactMinus2608.checked2618,CompactMinus2608.small2618,CompactMinus2608.nodes2618,NodeMinus40.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2608.p2619,GridMinus.atNode 2619,GridMinus.atNode 2620,NodeMinus40.w59,CompactMinus2608.checked2619,CompactMinus2608.small2619,CompactMinus2608.nodes2619,NodeMinus40.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2608.p2620,GridMinus.atNode 2620,GridMinus.atNode 2621,NodeMinus40.w60,CompactMinus2608.checked2620,CompactMinus2608.small2620,CompactMinus2608.nodes2620,NodeMinus40.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2608.p2621,GridMinus.atNode 2621,GridMinus.atNode 2622,NodeMinus40.w61,CompactMinus2608.checked2621,CompactMinus2608.small2621,CompactMinus2608.nodes2621,NodeMinus40.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2608.p2622,GridMinus.atNode 2622,GridMinus.atNode 2623,NodeMinus40.w62,CompactMinus2608.checked2622,CompactMinus2608.small2622,CompactMinus2608.nodes2622,NodeMinus40.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2608.p2623,GridMinus.atNode 2623,GridMinus.atNode 2624,NodeMinus40.w63,CompactMinus2608.checked2623,CompactMinus2608.small2623,CompactMinus2608.nodes2623,NodeMinus40.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (2560+j) ∧
    (atRow j).right=GridMinus.atNode (2560+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus40
