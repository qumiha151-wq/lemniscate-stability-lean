import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus2688
import SolitonClassification.Rotating.ResetPackedPlus2704
import SolitonClassification.Rotating.ResetPackedPlus2720
import SolitonClassification.Rotating.ResetPackedPlus2736
namespace SolitonClassification.Rotating.DyadicReset.TilePlus42
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus2688.p2688,GridPlus.atNode 2688,GridPlus.atNode 2689,NodePlus42.w0,CompactPlus2688.checked2688,CompactPlus2688.small2688,CompactPlus2688.nodes2688,NodePlus42.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus2688.p2689,GridPlus.atNode 2689,GridPlus.atNode 2690,NodePlus42.w1,CompactPlus2688.checked2689,CompactPlus2688.small2689,CompactPlus2688.nodes2689,NodePlus42.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus2688.p2690,GridPlus.atNode 2690,GridPlus.atNode 2691,NodePlus42.w2,CompactPlus2688.checked2690,CompactPlus2688.small2690,CompactPlus2688.nodes2690,NodePlus42.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus2688.p2691,GridPlus.atNode 2691,GridPlus.atNode 2692,NodePlus42.w3,CompactPlus2688.checked2691,CompactPlus2688.small2691,CompactPlus2688.nodes2691,NodePlus42.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus2688.p2692,GridPlus.atNode 2692,GridPlus.atNode 2693,NodePlus42.w4,CompactPlus2688.checked2692,CompactPlus2688.small2692,CompactPlus2688.nodes2692,NodePlus42.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus2688.p2693,GridPlus.atNode 2693,GridPlus.atNode 2694,NodePlus42.w5,CompactPlus2688.checked2693,CompactPlus2688.small2693,CompactPlus2688.nodes2693,NodePlus42.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus2688.p2694,GridPlus.atNode 2694,GridPlus.atNode 2695,NodePlus42.w6,CompactPlus2688.checked2694,CompactPlus2688.small2694,CompactPlus2688.nodes2694,NodePlus42.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus2688.p2695,GridPlus.atNode 2695,GridPlus.atNode 2696,NodePlus42.w7,CompactPlus2688.checked2695,CompactPlus2688.small2695,CompactPlus2688.nodes2695,NodePlus42.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus2688.p2696,GridPlus.atNode 2696,GridPlus.atNode 2697,NodePlus42.w8,CompactPlus2688.checked2696,CompactPlus2688.small2696,CompactPlus2688.nodes2696,NodePlus42.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus2688.p2697,GridPlus.atNode 2697,GridPlus.atNode 2698,NodePlus42.w9,CompactPlus2688.checked2697,CompactPlus2688.small2697,CompactPlus2688.nodes2697,NodePlus42.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus2688.p2698,GridPlus.atNode 2698,GridPlus.atNode 2699,NodePlus42.w10,CompactPlus2688.checked2698,CompactPlus2688.small2698,CompactPlus2688.nodes2698,NodePlus42.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus2688.p2699,GridPlus.atNode 2699,GridPlus.atNode 2700,NodePlus42.w11,CompactPlus2688.checked2699,CompactPlus2688.small2699,CompactPlus2688.nodes2699,NodePlus42.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus2688.p2700,GridPlus.atNode 2700,GridPlus.atNode 2701,NodePlus42.w12,CompactPlus2688.checked2700,CompactPlus2688.small2700,CompactPlus2688.nodes2700,NodePlus42.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus2688.p2701,GridPlus.atNode 2701,GridPlus.atNode 2702,NodePlus42.w13,CompactPlus2688.checked2701,CompactPlus2688.small2701,CompactPlus2688.nodes2701,NodePlus42.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus2688.p2702,GridPlus.atNode 2702,GridPlus.atNode 2703,NodePlus42.w14,CompactPlus2688.checked2702,CompactPlus2688.small2702,CompactPlus2688.nodes2702,NodePlus42.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus2688.p2703,GridPlus.atNode 2703,GridPlus.atNode 2704,NodePlus42.w15,CompactPlus2688.checked2703,CompactPlus2688.small2703,CompactPlus2688.nodes2703,NodePlus42.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus2704.p2704,GridPlus.atNode 2704,GridPlus.atNode 2705,NodePlus42.w16,CompactPlus2704.checked2704,CompactPlus2704.small2704,CompactPlus2704.nodes2704,NodePlus42.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus2704.p2705,GridPlus.atNode 2705,GridPlus.atNode 2706,NodePlus42.w17,CompactPlus2704.checked2705,CompactPlus2704.small2705,CompactPlus2704.nodes2705,NodePlus42.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus2704.p2706,GridPlus.atNode 2706,GridPlus.atNode 2707,NodePlus42.w18,CompactPlus2704.checked2706,CompactPlus2704.small2706,CompactPlus2704.nodes2706,NodePlus42.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus2704.p2707,GridPlus.atNode 2707,GridPlus.atNode 2708,NodePlus42.w19,CompactPlus2704.checked2707,CompactPlus2704.small2707,CompactPlus2704.nodes2707,NodePlus42.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus2704.p2708,GridPlus.atNode 2708,GridPlus.atNode 2709,NodePlus42.w20,CompactPlus2704.checked2708,CompactPlus2704.small2708,CompactPlus2704.nodes2708,NodePlus42.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus2704.p2709,GridPlus.atNode 2709,GridPlus.atNode 2710,NodePlus42.w21,CompactPlus2704.checked2709,CompactPlus2704.small2709,CompactPlus2704.nodes2709,NodePlus42.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus2704.p2710,GridPlus.atNode 2710,GridPlus.atNode 2711,NodePlus42.w22,CompactPlus2704.checked2710,CompactPlus2704.small2710,CompactPlus2704.nodes2710,NodePlus42.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus2704.p2711,GridPlus.atNode 2711,GridPlus.atNode 2712,NodePlus42.w23,CompactPlus2704.checked2711,CompactPlus2704.small2711,CompactPlus2704.nodes2711,NodePlus42.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus2704.p2712,GridPlus.atNode 2712,GridPlus.atNode 2713,NodePlus42.w24,CompactPlus2704.checked2712,CompactPlus2704.small2712,CompactPlus2704.nodes2712,NodePlus42.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus2704.p2713,GridPlus.atNode 2713,GridPlus.atNode 2714,NodePlus42.w25,CompactPlus2704.checked2713,CompactPlus2704.small2713,CompactPlus2704.nodes2713,NodePlus42.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus2704.p2714,GridPlus.atNode 2714,GridPlus.atNode 2715,NodePlus42.w26,CompactPlus2704.checked2714,CompactPlus2704.small2714,CompactPlus2704.nodes2714,NodePlus42.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus2704.p2715,GridPlus.atNode 2715,GridPlus.atNode 2716,NodePlus42.w27,CompactPlus2704.checked2715,CompactPlus2704.small2715,CompactPlus2704.nodes2715,NodePlus42.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus2704.p2716,GridPlus.atNode 2716,GridPlus.atNode 2717,NodePlus42.w28,CompactPlus2704.checked2716,CompactPlus2704.small2716,CompactPlus2704.nodes2716,NodePlus42.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus2704.p2717,GridPlus.atNode 2717,GridPlus.atNode 2718,NodePlus42.w29,CompactPlus2704.checked2717,CompactPlus2704.small2717,CompactPlus2704.nodes2717,NodePlus42.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus2704.p2718,GridPlus.atNode 2718,GridPlus.atNode 2719,NodePlus42.w30,CompactPlus2704.checked2718,CompactPlus2704.small2718,CompactPlus2704.nodes2718,NodePlus42.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus2704.p2719,GridPlus.atNode 2719,GridPlus.atNode 2720,NodePlus42.w31,CompactPlus2704.checked2719,CompactPlus2704.small2719,CompactPlus2704.nodes2719,NodePlus42.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus2720.p2720,GridPlus.atNode 2720,GridPlus.atNode 2721,NodePlus42.w32,CompactPlus2720.checked2720,CompactPlus2720.small2720,CompactPlus2720.nodes2720,NodePlus42.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus2720.p2721,GridPlus.atNode 2721,GridPlus.atNode 2722,NodePlus42.w33,CompactPlus2720.checked2721,CompactPlus2720.small2721,CompactPlus2720.nodes2721,NodePlus42.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus2720.p2722,GridPlus.atNode 2722,GridPlus.atNode 2723,NodePlus42.w34,CompactPlus2720.checked2722,CompactPlus2720.small2722,CompactPlus2720.nodes2722,NodePlus42.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus2720.p2723,GridPlus.atNode 2723,GridPlus.atNode 2724,NodePlus42.w35,CompactPlus2720.checked2723,CompactPlus2720.small2723,CompactPlus2720.nodes2723,NodePlus42.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus2720.p2724,GridPlus.atNode 2724,GridPlus.atNode 2725,NodePlus42.w36,CompactPlus2720.checked2724,CompactPlus2720.small2724,CompactPlus2720.nodes2724,NodePlus42.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus2720.p2725,GridPlus.atNode 2725,GridPlus.atNode 2726,NodePlus42.w37,CompactPlus2720.checked2725,CompactPlus2720.small2725,CompactPlus2720.nodes2725,NodePlus42.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus2720.p2726,GridPlus.atNode 2726,GridPlus.atNode 2727,NodePlus42.w38,CompactPlus2720.checked2726,CompactPlus2720.small2726,CompactPlus2720.nodes2726,NodePlus42.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus2720.p2727,GridPlus.atNode 2727,GridPlus.atNode 2728,NodePlus42.w39,CompactPlus2720.checked2727,CompactPlus2720.small2727,CompactPlus2720.nodes2727,NodePlus42.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus2720.p2728,GridPlus.atNode 2728,GridPlus.atNode 2729,NodePlus42.w40,CompactPlus2720.checked2728,CompactPlus2720.small2728,CompactPlus2720.nodes2728,NodePlus42.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus2720.p2729,GridPlus.atNode 2729,GridPlus.atNode 2730,NodePlus42.w41,CompactPlus2720.checked2729,CompactPlus2720.small2729,CompactPlus2720.nodes2729,NodePlus42.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus2720.p2730,GridPlus.atNode 2730,GridPlus.atNode 2731,NodePlus42.w42,CompactPlus2720.checked2730,CompactPlus2720.small2730,CompactPlus2720.nodes2730,NodePlus42.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus2720.p2731,GridPlus.atNode 2731,GridPlus.atNode 2732,NodePlus42.w43,CompactPlus2720.checked2731,CompactPlus2720.small2731,CompactPlus2720.nodes2731,NodePlus42.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus2720.p2732,GridPlus.atNode 2732,GridPlus.atNode 2733,NodePlus42.w44,CompactPlus2720.checked2732,CompactPlus2720.small2732,CompactPlus2720.nodes2732,NodePlus42.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus2720.p2733,GridPlus.atNode 2733,GridPlus.atNode 2734,NodePlus42.w45,CompactPlus2720.checked2733,CompactPlus2720.small2733,CompactPlus2720.nodes2733,NodePlus42.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus2720.p2734,GridPlus.atNode 2734,GridPlus.atNode 2735,NodePlus42.w46,CompactPlus2720.checked2734,CompactPlus2720.small2734,CompactPlus2720.nodes2734,NodePlus42.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus2720.p2735,GridPlus.atNode 2735,GridPlus.atNode 2736,NodePlus42.w47,CompactPlus2720.checked2735,CompactPlus2720.small2735,CompactPlus2720.nodes2735,NodePlus42.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus2736.p2736,GridPlus.atNode 2736,GridPlus.atNode 2737,NodePlus42.w48,CompactPlus2736.checked2736,CompactPlus2736.small2736,CompactPlus2736.nodes2736,NodePlus42.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus2736.p2737,GridPlus.atNode 2737,GridPlus.atNode 2738,NodePlus42.w49,CompactPlus2736.checked2737,CompactPlus2736.small2737,CompactPlus2736.nodes2737,NodePlus42.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus2736.p2738,GridPlus.atNode 2738,GridPlus.atNode 2739,NodePlus42.w50,CompactPlus2736.checked2738,CompactPlus2736.small2738,CompactPlus2736.nodes2738,NodePlus42.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus2736.p2739,GridPlus.atNode 2739,GridPlus.atNode 2740,NodePlus42.w51,CompactPlus2736.checked2739,CompactPlus2736.small2739,CompactPlus2736.nodes2739,NodePlus42.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus2736.p2740,GridPlus.atNode 2740,GridPlus.atNode 2741,NodePlus42.w52,CompactPlus2736.checked2740,CompactPlus2736.small2740,CompactPlus2736.nodes2740,NodePlus42.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus2736.p2741,GridPlus.atNode 2741,GridPlus.atNode 2742,NodePlus42.w53,CompactPlus2736.checked2741,CompactPlus2736.small2741,CompactPlus2736.nodes2741,NodePlus42.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus2736.p2742,GridPlus.atNode 2742,GridPlus.atNode 2743,NodePlus42.w54,CompactPlus2736.checked2742,CompactPlus2736.small2742,CompactPlus2736.nodes2742,NodePlus42.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus2736.p2743,GridPlus.atNode 2743,GridPlus.atNode 2744,NodePlus42.w55,CompactPlus2736.checked2743,CompactPlus2736.small2743,CompactPlus2736.nodes2743,NodePlus42.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus2736.p2744,GridPlus.atNode 2744,GridPlus.atNode 2745,NodePlus42.w56,CompactPlus2736.checked2744,CompactPlus2736.small2744,CompactPlus2736.nodes2744,NodePlus42.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus2736.p2745,GridPlus.atNode 2745,GridPlus.atNode 2746,NodePlus42.w57,CompactPlus2736.checked2745,CompactPlus2736.small2745,CompactPlus2736.nodes2745,NodePlus42.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus2736.p2746,GridPlus.atNode 2746,GridPlus.atNode 2747,NodePlus42.w58,CompactPlus2736.checked2746,CompactPlus2736.small2746,CompactPlus2736.nodes2746,NodePlus42.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus2736.p2747,GridPlus.atNode 2747,GridPlus.atNode 2748,NodePlus42.w59,CompactPlus2736.checked2747,CompactPlus2736.small2747,CompactPlus2736.nodes2747,NodePlus42.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus2736.p2748,GridPlus.atNode 2748,GridPlus.atNode 2749,NodePlus42.w60,CompactPlus2736.checked2748,CompactPlus2736.small2748,CompactPlus2736.nodes2748,NodePlus42.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus2736.p2749,GridPlus.atNode 2749,GridPlus.atNode 2750,NodePlus42.w61,CompactPlus2736.checked2749,CompactPlus2736.small2749,CompactPlus2736.nodes2749,NodePlus42.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus2736.p2750,GridPlus.atNode 2750,GridPlus.atNode 2751,NodePlus42.w62,CompactPlus2736.checked2750,CompactPlus2736.small2750,CompactPlus2736.nodes2750,NodePlus42.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus2736.p2751,GridPlus.atNode 2751,GridPlus.atNode 2752,NodePlus42.w63,CompactPlus2736.checked2751,CompactPlus2736.small2751,CompactPlus2736.nodes2751,NodePlus42.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (2688+j) ∧
    (atRow j).right=GridPlus.atNode (2688+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus42
