import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus2624
import SolitonClassification.Rotating.ResetPackedMinus2640
import SolitonClassification.Rotating.ResetPackedMinus2656
import SolitonClassification.Rotating.ResetPackedMinus2672
namespace SolitonClassification.Rotating.DyadicReset.TileMinus41
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2624.p2624,GridMinus.atNode 2624,GridMinus.atNode 2625,NodeMinus41.w0,CompactMinus2624.checked2624,CompactMinus2624.small2624,CompactMinus2624.nodes2624,NodeMinus41.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2624.p2625,GridMinus.atNode 2625,GridMinus.atNode 2626,NodeMinus41.w1,CompactMinus2624.checked2625,CompactMinus2624.small2625,CompactMinus2624.nodes2625,NodeMinus41.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2624.p2626,GridMinus.atNode 2626,GridMinus.atNode 2627,NodeMinus41.w2,CompactMinus2624.checked2626,CompactMinus2624.small2626,CompactMinus2624.nodes2626,NodeMinus41.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2624.p2627,GridMinus.atNode 2627,GridMinus.atNode 2628,NodeMinus41.w3,CompactMinus2624.checked2627,CompactMinus2624.small2627,CompactMinus2624.nodes2627,NodeMinus41.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2624.p2628,GridMinus.atNode 2628,GridMinus.atNode 2629,NodeMinus41.w4,CompactMinus2624.checked2628,CompactMinus2624.small2628,CompactMinus2624.nodes2628,NodeMinus41.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2624.p2629,GridMinus.atNode 2629,GridMinus.atNode 2630,NodeMinus41.w5,CompactMinus2624.checked2629,CompactMinus2624.small2629,CompactMinus2624.nodes2629,NodeMinus41.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2624.p2630,GridMinus.atNode 2630,GridMinus.atNode 2631,NodeMinus41.w6,CompactMinus2624.checked2630,CompactMinus2624.small2630,CompactMinus2624.nodes2630,NodeMinus41.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2624.p2631,GridMinus.atNode 2631,GridMinus.atNode 2632,NodeMinus41.w7,CompactMinus2624.checked2631,CompactMinus2624.small2631,CompactMinus2624.nodes2631,NodeMinus41.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2624.p2632,GridMinus.atNode 2632,GridMinus.atNode 2633,NodeMinus41.w8,CompactMinus2624.checked2632,CompactMinus2624.small2632,CompactMinus2624.nodes2632,NodeMinus41.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2624.p2633,GridMinus.atNode 2633,GridMinus.atNode 2634,NodeMinus41.w9,CompactMinus2624.checked2633,CompactMinus2624.small2633,CompactMinus2624.nodes2633,NodeMinus41.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2624.p2634,GridMinus.atNode 2634,GridMinus.atNode 2635,NodeMinus41.w10,CompactMinus2624.checked2634,CompactMinus2624.small2634,CompactMinus2624.nodes2634,NodeMinus41.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2624.p2635,GridMinus.atNode 2635,GridMinus.atNode 2636,NodeMinus41.w11,CompactMinus2624.checked2635,CompactMinus2624.small2635,CompactMinus2624.nodes2635,NodeMinus41.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2624.p2636,GridMinus.atNode 2636,GridMinus.atNode 2637,NodeMinus41.w12,CompactMinus2624.checked2636,CompactMinus2624.small2636,CompactMinus2624.nodes2636,NodeMinus41.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2624.p2637,GridMinus.atNode 2637,GridMinus.atNode 2638,NodeMinus41.w13,CompactMinus2624.checked2637,CompactMinus2624.small2637,CompactMinus2624.nodes2637,NodeMinus41.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2624.p2638,GridMinus.atNode 2638,GridMinus.atNode 2639,NodeMinus41.w14,CompactMinus2624.checked2638,CompactMinus2624.small2638,CompactMinus2624.nodes2638,NodeMinus41.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2624.p2639,GridMinus.atNode 2639,GridMinus.atNode 2640,NodeMinus41.w15,CompactMinus2624.checked2639,CompactMinus2624.small2639,CompactMinus2624.nodes2639,NodeMinus41.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2640.p2640,GridMinus.atNode 2640,GridMinus.atNode 2641,NodeMinus41.w16,CompactMinus2640.checked2640,CompactMinus2640.small2640,CompactMinus2640.nodes2640,NodeMinus41.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2640.p2641,GridMinus.atNode 2641,GridMinus.atNode 2642,NodeMinus41.w17,CompactMinus2640.checked2641,CompactMinus2640.small2641,CompactMinus2640.nodes2641,NodeMinus41.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2640.p2642,GridMinus.atNode 2642,GridMinus.atNode 2643,NodeMinus41.w18,CompactMinus2640.checked2642,CompactMinus2640.small2642,CompactMinus2640.nodes2642,NodeMinus41.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2640.p2643,GridMinus.atNode 2643,GridMinus.atNode 2644,NodeMinus41.w19,CompactMinus2640.checked2643,CompactMinus2640.small2643,CompactMinus2640.nodes2643,NodeMinus41.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2640.p2644,GridMinus.atNode 2644,GridMinus.atNode 2645,NodeMinus41.w20,CompactMinus2640.checked2644,CompactMinus2640.small2644,CompactMinus2640.nodes2644,NodeMinus41.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2640.p2645,GridMinus.atNode 2645,GridMinus.atNode 2646,NodeMinus41.w21,CompactMinus2640.checked2645,CompactMinus2640.small2645,CompactMinus2640.nodes2645,NodeMinus41.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2640.p2646,GridMinus.atNode 2646,GridMinus.atNode 2647,NodeMinus41.w22,CompactMinus2640.checked2646,CompactMinus2640.small2646,CompactMinus2640.nodes2646,NodeMinus41.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2640.p2647,GridMinus.atNode 2647,GridMinus.atNode 2648,NodeMinus41.w23,CompactMinus2640.checked2647,CompactMinus2640.small2647,CompactMinus2640.nodes2647,NodeMinus41.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2640.p2648,GridMinus.atNode 2648,GridMinus.atNode 2649,NodeMinus41.w24,CompactMinus2640.checked2648,CompactMinus2640.small2648,CompactMinus2640.nodes2648,NodeMinus41.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2640.p2649,GridMinus.atNode 2649,GridMinus.atNode 2650,NodeMinus41.w25,CompactMinus2640.checked2649,CompactMinus2640.small2649,CompactMinus2640.nodes2649,NodeMinus41.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2640.p2650,GridMinus.atNode 2650,GridMinus.atNode 2651,NodeMinus41.w26,CompactMinus2640.checked2650,CompactMinus2640.small2650,CompactMinus2640.nodes2650,NodeMinus41.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2640.p2651,GridMinus.atNode 2651,GridMinus.atNode 2652,NodeMinus41.w27,CompactMinus2640.checked2651,CompactMinus2640.small2651,CompactMinus2640.nodes2651,NodeMinus41.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2640.p2652,GridMinus.atNode 2652,GridMinus.atNode 2653,NodeMinus41.w28,CompactMinus2640.checked2652,CompactMinus2640.small2652,CompactMinus2640.nodes2652,NodeMinus41.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2640.p2653,GridMinus.atNode 2653,GridMinus.atNode 2654,NodeMinus41.w29,CompactMinus2640.checked2653,CompactMinus2640.small2653,CompactMinus2640.nodes2653,NodeMinus41.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2640.p2654,GridMinus.atNode 2654,GridMinus.atNode 2655,NodeMinus41.w30,CompactMinus2640.checked2654,CompactMinus2640.small2654,CompactMinus2640.nodes2654,NodeMinus41.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2640.p2655,GridMinus.atNode 2655,GridMinus.atNode 2656,NodeMinus41.w31,CompactMinus2640.checked2655,CompactMinus2640.small2655,CompactMinus2640.nodes2655,NodeMinus41.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2656.p2656,GridMinus.atNode 2656,GridMinus.atNode 2657,NodeMinus41.w32,CompactMinus2656.checked2656,CompactMinus2656.small2656,CompactMinus2656.nodes2656,NodeMinus41.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2656.p2657,GridMinus.atNode 2657,GridMinus.atNode 2658,NodeMinus41.w33,CompactMinus2656.checked2657,CompactMinus2656.small2657,CompactMinus2656.nodes2657,NodeMinus41.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2656.p2658,GridMinus.atNode 2658,GridMinus.atNode 2659,NodeMinus41.w34,CompactMinus2656.checked2658,CompactMinus2656.small2658,CompactMinus2656.nodes2658,NodeMinus41.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2656.p2659,GridMinus.atNode 2659,GridMinus.atNode 2660,NodeMinus41.w35,CompactMinus2656.checked2659,CompactMinus2656.small2659,CompactMinus2656.nodes2659,NodeMinus41.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2656.p2660,GridMinus.atNode 2660,GridMinus.atNode 2661,NodeMinus41.w36,CompactMinus2656.checked2660,CompactMinus2656.small2660,CompactMinus2656.nodes2660,NodeMinus41.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2656.p2661,GridMinus.atNode 2661,GridMinus.atNode 2662,NodeMinus41.w37,CompactMinus2656.checked2661,CompactMinus2656.small2661,CompactMinus2656.nodes2661,NodeMinus41.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2656.p2662,GridMinus.atNode 2662,GridMinus.atNode 2663,NodeMinus41.w38,CompactMinus2656.checked2662,CompactMinus2656.small2662,CompactMinus2656.nodes2662,NodeMinus41.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2656.p2663,GridMinus.atNode 2663,GridMinus.atNode 2664,NodeMinus41.w39,CompactMinus2656.checked2663,CompactMinus2656.small2663,CompactMinus2656.nodes2663,NodeMinus41.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2656.p2664,GridMinus.atNode 2664,GridMinus.atNode 2665,NodeMinus41.w40,CompactMinus2656.checked2664,CompactMinus2656.small2664,CompactMinus2656.nodes2664,NodeMinus41.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2656.p2665,GridMinus.atNode 2665,GridMinus.atNode 2666,NodeMinus41.w41,CompactMinus2656.checked2665,CompactMinus2656.small2665,CompactMinus2656.nodes2665,NodeMinus41.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2656.p2666,GridMinus.atNode 2666,GridMinus.atNode 2667,NodeMinus41.w42,CompactMinus2656.checked2666,CompactMinus2656.small2666,CompactMinus2656.nodes2666,NodeMinus41.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2656.p2667,GridMinus.atNode 2667,GridMinus.atNode 2668,NodeMinus41.w43,CompactMinus2656.checked2667,CompactMinus2656.small2667,CompactMinus2656.nodes2667,NodeMinus41.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2656.p2668,GridMinus.atNode 2668,GridMinus.atNode 2669,NodeMinus41.w44,CompactMinus2656.checked2668,CompactMinus2656.small2668,CompactMinus2656.nodes2668,NodeMinus41.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2656.p2669,GridMinus.atNode 2669,GridMinus.atNode 2670,NodeMinus41.w45,CompactMinus2656.checked2669,CompactMinus2656.small2669,CompactMinus2656.nodes2669,NodeMinus41.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2656.p2670,GridMinus.atNode 2670,GridMinus.atNode 2671,NodeMinus41.w46,CompactMinus2656.checked2670,CompactMinus2656.small2670,CompactMinus2656.nodes2670,NodeMinus41.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2656.p2671,GridMinus.atNode 2671,GridMinus.atNode 2672,NodeMinus41.w47,CompactMinus2656.checked2671,CompactMinus2656.small2671,CompactMinus2656.nodes2671,NodeMinus41.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2672.p2672,GridMinus.atNode 2672,GridMinus.atNode 2673,NodeMinus41.w48,CompactMinus2672.checked2672,CompactMinus2672.small2672,CompactMinus2672.nodes2672,NodeMinus41.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2672.p2673,GridMinus.atNode 2673,GridMinus.atNode 2674,NodeMinus41.w49,CompactMinus2672.checked2673,CompactMinus2672.small2673,CompactMinus2672.nodes2673,NodeMinus41.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2672.p2674,GridMinus.atNode 2674,GridMinus.atNode 2675,NodeMinus41.w50,CompactMinus2672.checked2674,CompactMinus2672.small2674,CompactMinus2672.nodes2674,NodeMinus41.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2672.p2675,GridMinus.atNode 2675,GridMinus.atNode 2676,NodeMinus41.w51,CompactMinus2672.checked2675,CompactMinus2672.small2675,CompactMinus2672.nodes2675,NodeMinus41.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2672.p2676,GridMinus.atNode 2676,GridMinus.atNode 2677,NodeMinus41.w52,CompactMinus2672.checked2676,CompactMinus2672.small2676,CompactMinus2672.nodes2676,NodeMinus41.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2672.p2677,GridMinus.atNode 2677,GridMinus.atNode 2678,NodeMinus41.w53,CompactMinus2672.checked2677,CompactMinus2672.small2677,CompactMinus2672.nodes2677,NodeMinus41.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2672.p2678,GridMinus.atNode 2678,GridMinus.atNode 2679,NodeMinus41.w54,CompactMinus2672.checked2678,CompactMinus2672.small2678,CompactMinus2672.nodes2678,NodeMinus41.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2672.p2679,GridMinus.atNode 2679,GridMinus.atNode 2680,NodeMinus41.w55,CompactMinus2672.checked2679,CompactMinus2672.small2679,CompactMinus2672.nodes2679,NodeMinus41.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2672.p2680,GridMinus.atNode 2680,GridMinus.atNode 2681,NodeMinus41.w56,CompactMinus2672.checked2680,CompactMinus2672.small2680,CompactMinus2672.nodes2680,NodeMinus41.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2672.p2681,GridMinus.atNode 2681,GridMinus.atNode 2682,NodeMinus41.w57,CompactMinus2672.checked2681,CompactMinus2672.small2681,CompactMinus2672.nodes2681,NodeMinus41.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2672.p2682,GridMinus.atNode 2682,GridMinus.atNode 2683,NodeMinus41.w58,CompactMinus2672.checked2682,CompactMinus2672.small2682,CompactMinus2672.nodes2682,NodeMinus41.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2672.p2683,GridMinus.atNode 2683,GridMinus.atNode 2684,NodeMinus41.w59,CompactMinus2672.checked2683,CompactMinus2672.small2683,CompactMinus2672.nodes2683,NodeMinus41.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2672.p2684,GridMinus.atNode 2684,GridMinus.atNode 2685,NodeMinus41.w60,CompactMinus2672.checked2684,CompactMinus2672.small2684,CompactMinus2672.nodes2684,NodeMinus41.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2672.p2685,GridMinus.atNode 2685,GridMinus.atNode 2686,NodeMinus41.w61,CompactMinus2672.checked2685,CompactMinus2672.small2685,CompactMinus2672.nodes2685,NodeMinus41.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2672.p2686,GridMinus.atNode 2686,GridMinus.atNode 2687,NodeMinus41.w62,CompactMinus2672.checked2686,CompactMinus2672.small2686,CompactMinus2672.nodes2686,NodeMinus41.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2672.p2687,GridMinus.atNode 2687,GridMinus.atNode 2688,NodeMinus41.w63,CompactMinus2672.checked2687,CompactMinus2672.small2687,CompactMinus2672.nodes2687,NodeMinus41.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (2624+j) ∧
    (atRow j).right=GridMinus.atNode (2624+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus41
