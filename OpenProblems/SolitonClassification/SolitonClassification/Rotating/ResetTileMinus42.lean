import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus2688
import SolitonClassification.Rotating.ResetPackedMinus2704
import SolitonClassification.Rotating.ResetPackedMinus2720
import SolitonClassification.Rotating.ResetPackedMinus2736
namespace SolitonClassification.Rotating.DyadicReset.TileMinus42
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2688.p2688,GridMinus.atNode 2688,GridMinus.atNode 2689,NodeMinus42.w0,CompactMinus2688.checked2688,CompactMinus2688.small2688,CompactMinus2688.nodes2688,NodeMinus42.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2688.p2689,GridMinus.atNode 2689,GridMinus.atNode 2690,NodeMinus42.w1,CompactMinus2688.checked2689,CompactMinus2688.small2689,CompactMinus2688.nodes2689,NodeMinus42.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2688.p2690,GridMinus.atNode 2690,GridMinus.atNode 2691,NodeMinus42.w2,CompactMinus2688.checked2690,CompactMinus2688.small2690,CompactMinus2688.nodes2690,NodeMinus42.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2688.p2691,GridMinus.atNode 2691,GridMinus.atNode 2692,NodeMinus42.w3,CompactMinus2688.checked2691,CompactMinus2688.small2691,CompactMinus2688.nodes2691,NodeMinus42.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2688.p2692,GridMinus.atNode 2692,GridMinus.atNode 2693,NodeMinus42.w4,CompactMinus2688.checked2692,CompactMinus2688.small2692,CompactMinus2688.nodes2692,NodeMinus42.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2688.p2693,GridMinus.atNode 2693,GridMinus.atNode 2694,NodeMinus42.w5,CompactMinus2688.checked2693,CompactMinus2688.small2693,CompactMinus2688.nodes2693,NodeMinus42.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2688.p2694,GridMinus.atNode 2694,GridMinus.atNode 2695,NodeMinus42.w6,CompactMinus2688.checked2694,CompactMinus2688.small2694,CompactMinus2688.nodes2694,NodeMinus42.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2688.p2695,GridMinus.atNode 2695,GridMinus.atNode 2696,NodeMinus42.w7,CompactMinus2688.checked2695,CompactMinus2688.small2695,CompactMinus2688.nodes2695,NodeMinus42.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2688.p2696,GridMinus.atNode 2696,GridMinus.atNode 2697,NodeMinus42.w8,CompactMinus2688.checked2696,CompactMinus2688.small2696,CompactMinus2688.nodes2696,NodeMinus42.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2688.p2697,GridMinus.atNode 2697,GridMinus.atNode 2698,NodeMinus42.w9,CompactMinus2688.checked2697,CompactMinus2688.small2697,CompactMinus2688.nodes2697,NodeMinus42.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2688.p2698,GridMinus.atNode 2698,GridMinus.atNode 2699,NodeMinus42.w10,CompactMinus2688.checked2698,CompactMinus2688.small2698,CompactMinus2688.nodes2698,NodeMinus42.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2688.p2699,GridMinus.atNode 2699,GridMinus.atNode 2700,NodeMinus42.w11,CompactMinus2688.checked2699,CompactMinus2688.small2699,CompactMinus2688.nodes2699,NodeMinus42.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2688.p2700,GridMinus.atNode 2700,GridMinus.atNode 2701,NodeMinus42.w12,CompactMinus2688.checked2700,CompactMinus2688.small2700,CompactMinus2688.nodes2700,NodeMinus42.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2688.p2701,GridMinus.atNode 2701,GridMinus.atNode 2702,NodeMinus42.w13,CompactMinus2688.checked2701,CompactMinus2688.small2701,CompactMinus2688.nodes2701,NodeMinus42.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2688.p2702,GridMinus.atNode 2702,GridMinus.atNode 2703,NodeMinus42.w14,CompactMinus2688.checked2702,CompactMinus2688.small2702,CompactMinus2688.nodes2702,NodeMinus42.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2688.p2703,GridMinus.atNode 2703,GridMinus.atNode 2704,NodeMinus42.w15,CompactMinus2688.checked2703,CompactMinus2688.small2703,CompactMinus2688.nodes2703,NodeMinus42.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2704.p2704,GridMinus.atNode 2704,GridMinus.atNode 2705,NodeMinus42.w16,CompactMinus2704.checked2704,CompactMinus2704.small2704,CompactMinus2704.nodes2704,NodeMinus42.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2704.p2705,GridMinus.atNode 2705,GridMinus.atNode 2706,NodeMinus42.w17,CompactMinus2704.checked2705,CompactMinus2704.small2705,CompactMinus2704.nodes2705,NodeMinus42.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2704.p2706,GridMinus.atNode 2706,GridMinus.atNode 2707,NodeMinus42.w18,CompactMinus2704.checked2706,CompactMinus2704.small2706,CompactMinus2704.nodes2706,NodeMinus42.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2704.p2707,GridMinus.atNode 2707,GridMinus.atNode 2708,NodeMinus42.w19,CompactMinus2704.checked2707,CompactMinus2704.small2707,CompactMinus2704.nodes2707,NodeMinus42.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2704.p2708,GridMinus.atNode 2708,GridMinus.atNode 2709,NodeMinus42.w20,CompactMinus2704.checked2708,CompactMinus2704.small2708,CompactMinus2704.nodes2708,NodeMinus42.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2704.p2709,GridMinus.atNode 2709,GridMinus.atNode 2710,NodeMinus42.w21,CompactMinus2704.checked2709,CompactMinus2704.small2709,CompactMinus2704.nodes2709,NodeMinus42.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2704.p2710,GridMinus.atNode 2710,GridMinus.atNode 2711,NodeMinus42.w22,CompactMinus2704.checked2710,CompactMinus2704.small2710,CompactMinus2704.nodes2710,NodeMinus42.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2704.p2711,GridMinus.atNode 2711,GridMinus.atNode 2712,NodeMinus42.w23,CompactMinus2704.checked2711,CompactMinus2704.small2711,CompactMinus2704.nodes2711,NodeMinus42.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2704.p2712,GridMinus.atNode 2712,GridMinus.atNode 2713,NodeMinus42.w24,CompactMinus2704.checked2712,CompactMinus2704.small2712,CompactMinus2704.nodes2712,NodeMinus42.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2704.p2713,GridMinus.atNode 2713,GridMinus.atNode 2714,NodeMinus42.w25,CompactMinus2704.checked2713,CompactMinus2704.small2713,CompactMinus2704.nodes2713,NodeMinus42.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2704.p2714,GridMinus.atNode 2714,GridMinus.atNode 2715,NodeMinus42.w26,CompactMinus2704.checked2714,CompactMinus2704.small2714,CompactMinus2704.nodes2714,NodeMinus42.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2704.p2715,GridMinus.atNode 2715,GridMinus.atNode 2716,NodeMinus42.w27,CompactMinus2704.checked2715,CompactMinus2704.small2715,CompactMinus2704.nodes2715,NodeMinus42.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2704.p2716,GridMinus.atNode 2716,GridMinus.atNode 2717,NodeMinus42.w28,CompactMinus2704.checked2716,CompactMinus2704.small2716,CompactMinus2704.nodes2716,NodeMinus42.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2704.p2717,GridMinus.atNode 2717,GridMinus.atNode 2718,NodeMinus42.w29,CompactMinus2704.checked2717,CompactMinus2704.small2717,CompactMinus2704.nodes2717,NodeMinus42.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2704.p2718,GridMinus.atNode 2718,GridMinus.atNode 2719,NodeMinus42.w30,CompactMinus2704.checked2718,CompactMinus2704.small2718,CompactMinus2704.nodes2718,NodeMinus42.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2704.p2719,GridMinus.atNode 2719,GridMinus.atNode 2720,NodeMinus42.w31,CompactMinus2704.checked2719,CompactMinus2704.small2719,CompactMinus2704.nodes2719,NodeMinus42.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2720.p2720,GridMinus.atNode 2720,GridMinus.atNode 2721,NodeMinus42.w32,CompactMinus2720.checked2720,CompactMinus2720.small2720,CompactMinus2720.nodes2720,NodeMinus42.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2720.p2721,GridMinus.atNode 2721,GridMinus.atNode 2722,NodeMinus42.w33,CompactMinus2720.checked2721,CompactMinus2720.small2721,CompactMinus2720.nodes2721,NodeMinus42.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2720.p2722,GridMinus.atNode 2722,GridMinus.atNode 2723,NodeMinus42.w34,CompactMinus2720.checked2722,CompactMinus2720.small2722,CompactMinus2720.nodes2722,NodeMinus42.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2720.p2723,GridMinus.atNode 2723,GridMinus.atNode 2724,NodeMinus42.w35,CompactMinus2720.checked2723,CompactMinus2720.small2723,CompactMinus2720.nodes2723,NodeMinus42.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2720.p2724,GridMinus.atNode 2724,GridMinus.atNode 2725,NodeMinus42.w36,CompactMinus2720.checked2724,CompactMinus2720.small2724,CompactMinus2720.nodes2724,NodeMinus42.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2720.p2725,GridMinus.atNode 2725,GridMinus.atNode 2726,NodeMinus42.w37,CompactMinus2720.checked2725,CompactMinus2720.small2725,CompactMinus2720.nodes2725,NodeMinus42.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2720.p2726,GridMinus.atNode 2726,GridMinus.atNode 2727,NodeMinus42.w38,CompactMinus2720.checked2726,CompactMinus2720.small2726,CompactMinus2720.nodes2726,NodeMinus42.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2720.p2727,GridMinus.atNode 2727,GridMinus.atNode 2728,NodeMinus42.w39,CompactMinus2720.checked2727,CompactMinus2720.small2727,CompactMinus2720.nodes2727,NodeMinus42.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2720.p2728,GridMinus.atNode 2728,GridMinus.atNode 2729,NodeMinus42.w40,CompactMinus2720.checked2728,CompactMinus2720.small2728,CompactMinus2720.nodes2728,NodeMinus42.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2720.p2729,GridMinus.atNode 2729,GridMinus.atNode 2730,NodeMinus42.w41,CompactMinus2720.checked2729,CompactMinus2720.small2729,CompactMinus2720.nodes2729,NodeMinus42.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2720.p2730,GridMinus.atNode 2730,GridMinus.atNode 2731,NodeMinus42.w42,CompactMinus2720.checked2730,CompactMinus2720.small2730,CompactMinus2720.nodes2730,NodeMinus42.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2720.p2731,GridMinus.atNode 2731,GridMinus.atNode 2732,NodeMinus42.w43,CompactMinus2720.checked2731,CompactMinus2720.small2731,CompactMinus2720.nodes2731,NodeMinus42.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2720.p2732,GridMinus.atNode 2732,GridMinus.atNode 2733,NodeMinus42.w44,CompactMinus2720.checked2732,CompactMinus2720.small2732,CompactMinus2720.nodes2732,NodeMinus42.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2720.p2733,GridMinus.atNode 2733,GridMinus.atNode 2734,NodeMinus42.w45,CompactMinus2720.checked2733,CompactMinus2720.small2733,CompactMinus2720.nodes2733,NodeMinus42.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2720.p2734,GridMinus.atNode 2734,GridMinus.atNode 2735,NodeMinus42.w46,CompactMinus2720.checked2734,CompactMinus2720.small2734,CompactMinus2720.nodes2734,NodeMinus42.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2720.p2735,GridMinus.atNode 2735,GridMinus.atNode 2736,NodeMinus42.w47,CompactMinus2720.checked2735,CompactMinus2720.small2735,CompactMinus2720.nodes2735,NodeMinus42.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2736.p2736,GridMinus.atNode 2736,GridMinus.atNode 2737,NodeMinus42.w48,CompactMinus2736.checked2736,CompactMinus2736.small2736,CompactMinus2736.nodes2736,NodeMinus42.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2736.p2737,GridMinus.atNode 2737,GridMinus.atNode 2738,NodeMinus42.w49,CompactMinus2736.checked2737,CompactMinus2736.small2737,CompactMinus2736.nodes2737,NodeMinus42.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2736.p2738,GridMinus.atNode 2738,GridMinus.atNode 2739,NodeMinus42.w50,CompactMinus2736.checked2738,CompactMinus2736.small2738,CompactMinus2736.nodes2738,NodeMinus42.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2736.p2739,GridMinus.atNode 2739,GridMinus.atNode 2740,NodeMinus42.w51,CompactMinus2736.checked2739,CompactMinus2736.small2739,CompactMinus2736.nodes2739,NodeMinus42.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2736.p2740,GridMinus.atNode 2740,GridMinus.atNode 2741,NodeMinus42.w52,CompactMinus2736.checked2740,CompactMinus2736.small2740,CompactMinus2736.nodes2740,NodeMinus42.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2736.p2741,GridMinus.atNode 2741,GridMinus.atNode 2742,NodeMinus42.w53,CompactMinus2736.checked2741,CompactMinus2736.small2741,CompactMinus2736.nodes2741,NodeMinus42.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2736.p2742,GridMinus.atNode 2742,GridMinus.atNode 2743,NodeMinus42.w54,CompactMinus2736.checked2742,CompactMinus2736.small2742,CompactMinus2736.nodes2742,NodeMinus42.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2736.p2743,GridMinus.atNode 2743,GridMinus.atNode 2744,NodeMinus42.w55,CompactMinus2736.checked2743,CompactMinus2736.small2743,CompactMinus2736.nodes2743,NodeMinus42.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2736.p2744,GridMinus.atNode 2744,GridMinus.atNode 2745,NodeMinus42.w56,CompactMinus2736.checked2744,CompactMinus2736.small2744,CompactMinus2736.nodes2744,NodeMinus42.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2736.p2745,GridMinus.atNode 2745,GridMinus.atNode 2746,NodeMinus42.w57,CompactMinus2736.checked2745,CompactMinus2736.small2745,CompactMinus2736.nodes2745,NodeMinus42.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2736.p2746,GridMinus.atNode 2746,GridMinus.atNode 2747,NodeMinus42.w58,CompactMinus2736.checked2746,CompactMinus2736.small2746,CompactMinus2736.nodes2746,NodeMinus42.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2736.p2747,GridMinus.atNode 2747,GridMinus.atNode 2748,NodeMinus42.w59,CompactMinus2736.checked2747,CompactMinus2736.small2747,CompactMinus2736.nodes2747,NodeMinus42.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2736.p2748,GridMinus.atNode 2748,GridMinus.atNode 2749,NodeMinus42.w60,CompactMinus2736.checked2748,CompactMinus2736.small2748,CompactMinus2736.nodes2748,NodeMinus42.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2736.p2749,GridMinus.atNode 2749,GridMinus.atNode 2750,NodeMinus42.w61,CompactMinus2736.checked2749,CompactMinus2736.small2749,CompactMinus2736.nodes2749,NodeMinus42.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2736.p2750,GridMinus.atNode 2750,GridMinus.atNode 2751,NodeMinus42.w62,CompactMinus2736.checked2750,CompactMinus2736.small2750,CompactMinus2736.nodes2750,NodeMinus42.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2736.p2751,GridMinus.atNode 2751,GridMinus.atNode 2752,NodeMinus42.w63,CompactMinus2736.checked2751,CompactMinus2736.small2751,CompactMinus2736.nodes2751,NodeMinus42.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (2688+j) ∧
    (atRow j).right=GridMinus.atNode (2688+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus42
