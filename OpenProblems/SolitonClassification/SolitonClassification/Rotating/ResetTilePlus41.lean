import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus2624
import SolitonClassification.Rotating.ResetPackedPlus2640
import SolitonClassification.Rotating.ResetPackedPlus2656
import SolitonClassification.Rotating.ResetPackedPlus2672
namespace SolitonClassification.Rotating.DyadicReset.TilePlus41
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus2624.p2624,GridPlus.atNode 2624,GridPlus.atNode 2625,NodePlus41.w0,CompactPlus2624.checked2624,CompactPlus2624.small2624,CompactPlus2624.nodes2624,NodePlus41.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus2624.p2625,GridPlus.atNode 2625,GridPlus.atNode 2626,NodePlus41.w1,CompactPlus2624.checked2625,CompactPlus2624.small2625,CompactPlus2624.nodes2625,NodePlus41.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus2624.p2626,GridPlus.atNode 2626,GridPlus.atNode 2627,NodePlus41.w2,CompactPlus2624.checked2626,CompactPlus2624.small2626,CompactPlus2624.nodes2626,NodePlus41.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus2624.p2627,GridPlus.atNode 2627,GridPlus.atNode 2628,NodePlus41.w3,CompactPlus2624.checked2627,CompactPlus2624.small2627,CompactPlus2624.nodes2627,NodePlus41.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus2624.p2628,GridPlus.atNode 2628,GridPlus.atNode 2629,NodePlus41.w4,CompactPlus2624.checked2628,CompactPlus2624.small2628,CompactPlus2624.nodes2628,NodePlus41.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus2624.p2629,GridPlus.atNode 2629,GridPlus.atNode 2630,NodePlus41.w5,CompactPlus2624.checked2629,CompactPlus2624.small2629,CompactPlus2624.nodes2629,NodePlus41.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus2624.p2630,GridPlus.atNode 2630,GridPlus.atNode 2631,NodePlus41.w6,CompactPlus2624.checked2630,CompactPlus2624.small2630,CompactPlus2624.nodes2630,NodePlus41.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus2624.p2631,GridPlus.atNode 2631,GridPlus.atNode 2632,NodePlus41.w7,CompactPlus2624.checked2631,CompactPlus2624.small2631,CompactPlus2624.nodes2631,NodePlus41.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus2624.p2632,GridPlus.atNode 2632,GridPlus.atNode 2633,NodePlus41.w8,CompactPlus2624.checked2632,CompactPlus2624.small2632,CompactPlus2624.nodes2632,NodePlus41.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus2624.p2633,GridPlus.atNode 2633,GridPlus.atNode 2634,NodePlus41.w9,CompactPlus2624.checked2633,CompactPlus2624.small2633,CompactPlus2624.nodes2633,NodePlus41.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus2624.p2634,GridPlus.atNode 2634,GridPlus.atNode 2635,NodePlus41.w10,CompactPlus2624.checked2634,CompactPlus2624.small2634,CompactPlus2624.nodes2634,NodePlus41.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus2624.p2635,GridPlus.atNode 2635,GridPlus.atNode 2636,NodePlus41.w11,CompactPlus2624.checked2635,CompactPlus2624.small2635,CompactPlus2624.nodes2635,NodePlus41.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus2624.p2636,GridPlus.atNode 2636,GridPlus.atNode 2637,NodePlus41.w12,CompactPlus2624.checked2636,CompactPlus2624.small2636,CompactPlus2624.nodes2636,NodePlus41.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus2624.p2637,GridPlus.atNode 2637,GridPlus.atNode 2638,NodePlus41.w13,CompactPlus2624.checked2637,CompactPlus2624.small2637,CompactPlus2624.nodes2637,NodePlus41.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus2624.p2638,GridPlus.atNode 2638,GridPlus.atNode 2639,NodePlus41.w14,CompactPlus2624.checked2638,CompactPlus2624.small2638,CompactPlus2624.nodes2638,NodePlus41.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus2624.p2639,GridPlus.atNode 2639,GridPlus.atNode 2640,NodePlus41.w15,CompactPlus2624.checked2639,CompactPlus2624.small2639,CompactPlus2624.nodes2639,NodePlus41.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus2640.p2640,GridPlus.atNode 2640,GridPlus.atNode 2641,NodePlus41.w16,CompactPlus2640.checked2640,CompactPlus2640.small2640,CompactPlus2640.nodes2640,NodePlus41.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus2640.p2641,GridPlus.atNode 2641,GridPlus.atNode 2642,NodePlus41.w17,CompactPlus2640.checked2641,CompactPlus2640.small2641,CompactPlus2640.nodes2641,NodePlus41.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus2640.p2642,GridPlus.atNode 2642,GridPlus.atNode 2643,NodePlus41.w18,CompactPlus2640.checked2642,CompactPlus2640.small2642,CompactPlus2640.nodes2642,NodePlus41.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus2640.p2643,GridPlus.atNode 2643,GridPlus.atNode 2644,NodePlus41.w19,CompactPlus2640.checked2643,CompactPlus2640.small2643,CompactPlus2640.nodes2643,NodePlus41.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus2640.p2644,GridPlus.atNode 2644,GridPlus.atNode 2645,NodePlus41.w20,CompactPlus2640.checked2644,CompactPlus2640.small2644,CompactPlus2640.nodes2644,NodePlus41.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus2640.p2645,GridPlus.atNode 2645,GridPlus.atNode 2646,NodePlus41.w21,CompactPlus2640.checked2645,CompactPlus2640.small2645,CompactPlus2640.nodes2645,NodePlus41.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus2640.p2646,GridPlus.atNode 2646,GridPlus.atNode 2647,NodePlus41.w22,CompactPlus2640.checked2646,CompactPlus2640.small2646,CompactPlus2640.nodes2646,NodePlus41.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus2640.p2647,GridPlus.atNode 2647,GridPlus.atNode 2648,NodePlus41.w23,CompactPlus2640.checked2647,CompactPlus2640.small2647,CompactPlus2640.nodes2647,NodePlus41.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus2640.p2648,GridPlus.atNode 2648,GridPlus.atNode 2649,NodePlus41.w24,CompactPlus2640.checked2648,CompactPlus2640.small2648,CompactPlus2640.nodes2648,NodePlus41.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus2640.p2649,GridPlus.atNode 2649,GridPlus.atNode 2650,NodePlus41.w25,CompactPlus2640.checked2649,CompactPlus2640.small2649,CompactPlus2640.nodes2649,NodePlus41.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus2640.p2650,GridPlus.atNode 2650,GridPlus.atNode 2651,NodePlus41.w26,CompactPlus2640.checked2650,CompactPlus2640.small2650,CompactPlus2640.nodes2650,NodePlus41.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus2640.p2651,GridPlus.atNode 2651,GridPlus.atNode 2652,NodePlus41.w27,CompactPlus2640.checked2651,CompactPlus2640.small2651,CompactPlus2640.nodes2651,NodePlus41.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus2640.p2652,GridPlus.atNode 2652,GridPlus.atNode 2653,NodePlus41.w28,CompactPlus2640.checked2652,CompactPlus2640.small2652,CompactPlus2640.nodes2652,NodePlus41.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus2640.p2653,GridPlus.atNode 2653,GridPlus.atNode 2654,NodePlus41.w29,CompactPlus2640.checked2653,CompactPlus2640.small2653,CompactPlus2640.nodes2653,NodePlus41.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus2640.p2654,GridPlus.atNode 2654,GridPlus.atNode 2655,NodePlus41.w30,CompactPlus2640.checked2654,CompactPlus2640.small2654,CompactPlus2640.nodes2654,NodePlus41.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus2640.p2655,GridPlus.atNode 2655,GridPlus.atNode 2656,NodePlus41.w31,CompactPlus2640.checked2655,CompactPlus2640.small2655,CompactPlus2640.nodes2655,NodePlus41.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus2656.p2656,GridPlus.atNode 2656,GridPlus.atNode 2657,NodePlus41.w32,CompactPlus2656.checked2656,CompactPlus2656.small2656,CompactPlus2656.nodes2656,NodePlus41.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus2656.p2657,GridPlus.atNode 2657,GridPlus.atNode 2658,NodePlus41.w33,CompactPlus2656.checked2657,CompactPlus2656.small2657,CompactPlus2656.nodes2657,NodePlus41.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus2656.p2658,GridPlus.atNode 2658,GridPlus.atNode 2659,NodePlus41.w34,CompactPlus2656.checked2658,CompactPlus2656.small2658,CompactPlus2656.nodes2658,NodePlus41.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus2656.p2659,GridPlus.atNode 2659,GridPlus.atNode 2660,NodePlus41.w35,CompactPlus2656.checked2659,CompactPlus2656.small2659,CompactPlus2656.nodes2659,NodePlus41.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus2656.p2660,GridPlus.atNode 2660,GridPlus.atNode 2661,NodePlus41.w36,CompactPlus2656.checked2660,CompactPlus2656.small2660,CompactPlus2656.nodes2660,NodePlus41.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus2656.p2661,GridPlus.atNode 2661,GridPlus.atNode 2662,NodePlus41.w37,CompactPlus2656.checked2661,CompactPlus2656.small2661,CompactPlus2656.nodes2661,NodePlus41.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus2656.p2662,GridPlus.atNode 2662,GridPlus.atNode 2663,NodePlus41.w38,CompactPlus2656.checked2662,CompactPlus2656.small2662,CompactPlus2656.nodes2662,NodePlus41.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus2656.p2663,GridPlus.atNode 2663,GridPlus.atNode 2664,NodePlus41.w39,CompactPlus2656.checked2663,CompactPlus2656.small2663,CompactPlus2656.nodes2663,NodePlus41.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus2656.p2664,GridPlus.atNode 2664,GridPlus.atNode 2665,NodePlus41.w40,CompactPlus2656.checked2664,CompactPlus2656.small2664,CompactPlus2656.nodes2664,NodePlus41.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus2656.p2665,GridPlus.atNode 2665,GridPlus.atNode 2666,NodePlus41.w41,CompactPlus2656.checked2665,CompactPlus2656.small2665,CompactPlus2656.nodes2665,NodePlus41.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus2656.p2666,GridPlus.atNode 2666,GridPlus.atNode 2667,NodePlus41.w42,CompactPlus2656.checked2666,CompactPlus2656.small2666,CompactPlus2656.nodes2666,NodePlus41.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus2656.p2667,GridPlus.atNode 2667,GridPlus.atNode 2668,NodePlus41.w43,CompactPlus2656.checked2667,CompactPlus2656.small2667,CompactPlus2656.nodes2667,NodePlus41.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus2656.p2668,GridPlus.atNode 2668,GridPlus.atNode 2669,NodePlus41.w44,CompactPlus2656.checked2668,CompactPlus2656.small2668,CompactPlus2656.nodes2668,NodePlus41.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus2656.p2669,GridPlus.atNode 2669,GridPlus.atNode 2670,NodePlus41.w45,CompactPlus2656.checked2669,CompactPlus2656.small2669,CompactPlus2656.nodes2669,NodePlus41.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus2656.p2670,GridPlus.atNode 2670,GridPlus.atNode 2671,NodePlus41.w46,CompactPlus2656.checked2670,CompactPlus2656.small2670,CompactPlus2656.nodes2670,NodePlus41.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus2656.p2671,GridPlus.atNode 2671,GridPlus.atNode 2672,NodePlus41.w47,CompactPlus2656.checked2671,CompactPlus2656.small2671,CompactPlus2656.nodes2671,NodePlus41.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus2672.p2672,GridPlus.atNode 2672,GridPlus.atNode 2673,NodePlus41.w48,CompactPlus2672.checked2672,CompactPlus2672.small2672,CompactPlus2672.nodes2672,NodePlus41.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus2672.p2673,GridPlus.atNode 2673,GridPlus.atNode 2674,NodePlus41.w49,CompactPlus2672.checked2673,CompactPlus2672.small2673,CompactPlus2672.nodes2673,NodePlus41.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus2672.p2674,GridPlus.atNode 2674,GridPlus.atNode 2675,NodePlus41.w50,CompactPlus2672.checked2674,CompactPlus2672.small2674,CompactPlus2672.nodes2674,NodePlus41.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus2672.p2675,GridPlus.atNode 2675,GridPlus.atNode 2676,NodePlus41.w51,CompactPlus2672.checked2675,CompactPlus2672.small2675,CompactPlus2672.nodes2675,NodePlus41.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus2672.p2676,GridPlus.atNode 2676,GridPlus.atNode 2677,NodePlus41.w52,CompactPlus2672.checked2676,CompactPlus2672.small2676,CompactPlus2672.nodes2676,NodePlus41.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus2672.p2677,GridPlus.atNode 2677,GridPlus.atNode 2678,NodePlus41.w53,CompactPlus2672.checked2677,CompactPlus2672.small2677,CompactPlus2672.nodes2677,NodePlus41.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus2672.p2678,GridPlus.atNode 2678,GridPlus.atNode 2679,NodePlus41.w54,CompactPlus2672.checked2678,CompactPlus2672.small2678,CompactPlus2672.nodes2678,NodePlus41.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus2672.p2679,GridPlus.atNode 2679,GridPlus.atNode 2680,NodePlus41.w55,CompactPlus2672.checked2679,CompactPlus2672.small2679,CompactPlus2672.nodes2679,NodePlus41.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus2672.p2680,GridPlus.atNode 2680,GridPlus.atNode 2681,NodePlus41.w56,CompactPlus2672.checked2680,CompactPlus2672.small2680,CompactPlus2672.nodes2680,NodePlus41.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus2672.p2681,GridPlus.atNode 2681,GridPlus.atNode 2682,NodePlus41.w57,CompactPlus2672.checked2681,CompactPlus2672.small2681,CompactPlus2672.nodes2681,NodePlus41.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus2672.p2682,GridPlus.atNode 2682,GridPlus.atNode 2683,NodePlus41.w58,CompactPlus2672.checked2682,CompactPlus2672.small2682,CompactPlus2672.nodes2682,NodePlus41.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus2672.p2683,GridPlus.atNode 2683,GridPlus.atNode 2684,NodePlus41.w59,CompactPlus2672.checked2683,CompactPlus2672.small2683,CompactPlus2672.nodes2683,NodePlus41.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus2672.p2684,GridPlus.atNode 2684,GridPlus.atNode 2685,NodePlus41.w60,CompactPlus2672.checked2684,CompactPlus2672.small2684,CompactPlus2672.nodes2684,NodePlus41.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus2672.p2685,GridPlus.atNode 2685,GridPlus.atNode 2686,NodePlus41.w61,CompactPlus2672.checked2685,CompactPlus2672.small2685,CompactPlus2672.nodes2685,NodePlus41.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus2672.p2686,GridPlus.atNode 2686,GridPlus.atNode 2687,NodePlus41.w62,CompactPlus2672.checked2686,CompactPlus2672.small2686,CompactPlus2672.nodes2686,NodePlus41.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus2672.p2687,GridPlus.atNode 2687,GridPlus.atNode 2688,NodePlus41.w63,CompactPlus2672.checked2687,CompactPlus2672.small2687,CompactPlus2672.nodes2687,NodePlus41.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (2624+j) ∧
    (atRow j).right=GridPlus.atNode (2624+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus41
