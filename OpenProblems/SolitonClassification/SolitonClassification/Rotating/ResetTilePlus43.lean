import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus2752
import SolitonClassification.Rotating.ResetPackedPlus2768
import SolitonClassification.Rotating.ResetPackedPlus2784
import SolitonClassification.Rotating.ResetPackedPlus2800
namespace SolitonClassification.Rotating.DyadicReset.TilePlus43
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus2752.p2752,GridPlus.atNode 2752,GridPlus.atNode 2753,NodePlus43.w0,CompactPlus2752.checked2752,CompactPlus2752.small2752,CompactPlus2752.nodes2752,NodePlus43.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus2752.p2753,GridPlus.atNode 2753,GridPlus.atNode 2754,NodePlus43.w1,CompactPlus2752.checked2753,CompactPlus2752.small2753,CompactPlus2752.nodes2753,NodePlus43.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus2752.p2754,GridPlus.atNode 2754,GridPlus.atNode 2755,NodePlus43.w2,CompactPlus2752.checked2754,CompactPlus2752.small2754,CompactPlus2752.nodes2754,NodePlus43.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus2752.p2755,GridPlus.atNode 2755,GridPlus.atNode 2756,NodePlus43.w3,CompactPlus2752.checked2755,CompactPlus2752.small2755,CompactPlus2752.nodes2755,NodePlus43.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus2752.p2756,GridPlus.atNode 2756,GridPlus.atNode 2757,NodePlus43.w4,CompactPlus2752.checked2756,CompactPlus2752.small2756,CompactPlus2752.nodes2756,NodePlus43.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus2752.p2757,GridPlus.atNode 2757,GridPlus.atNode 2758,NodePlus43.w5,CompactPlus2752.checked2757,CompactPlus2752.small2757,CompactPlus2752.nodes2757,NodePlus43.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus2752.p2758,GridPlus.atNode 2758,GridPlus.atNode 2759,NodePlus43.w6,CompactPlus2752.checked2758,CompactPlus2752.small2758,CompactPlus2752.nodes2758,NodePlus43.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus2752.p2759,GridPlus.atNode 2759,GridPlus.atNode 2760,NodePlus43.w7,CompactPlus2752.checked2759,CompactPlus2752.small2759,CompactPlus2752.nodes2759,NodePlus43.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus2752.p2760,GridPlus.atNode 2760,GridPlus.atNode 2761,NodePlus43.w8,CompactPlus2752.checked2760,CompactPlus2752.small2760,CompactPlus2752.nodes2760,NodePlus43.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus2752.p2761,GridPlus.atNode 2761,GridPlus.atNode 2762,NodePlus43.w9,CompactPlus2752.checked2761,CompactPlus2752.small2761,CompactPlus2752.nodes2761,NodePlus43.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus2752.p2762,GridPlus.atNode 2762,GridPlus.atNode 2763,NodePlus43.w10,CompactPlus2752.checked2762,CompactPlus2752.small2762,CompactPlus2752.nodes2762,NodePlus43.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus2752.p2763,GridPlus.atNode 2763,GridPlus.atNode 2764,NodePlus43.w11,CompactPlus2752.checked2763,CompactPlus2752.small2763,CompactPlus2752.nodes2763,NodePlus43.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus2752.p2764,GridPlus.atNode 2764,GridPlus.atNode 2765,NodePlus43.w12,CompactPlus2752.checked2764,CompactPlus2752.small2764,CompactPlus2752.nodes2764,NodePlus43.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus2752.p2765,GridPlus.atNode 2765,GridPlus.atNode 2766,NodePlus43.w13,CompactPlus2752.checked2765,CompactPlus2752.small2765,CompactPlus2752.nodes2765,NodePlus43.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus2752.p2766,GridPlus.atNode 2766,GridPlus.atNode 2767,NodePlus43.w14,CompactPlus2752.checked2766,CompactPlus2752.small2766,CompactPlus2752.nodes2766,NodePlus43.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus2752.p2767,GridPlus.atNode 2767,GridPlus.atNode 2768,NodePlus43.w15,CompactPlus2752.checked2767,CompactPlus2752.small2767,CompactPlus2752.nodes2767,NodePlus43.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus2768.p2768,GridPlus.atNode 2768,GridPlus.atNode 2769,NodePlus43.w16,CompactPlus2768.checked2768,CompactPlus2768.small2768,CompactPlus2768.nodes2768,NodePlus43.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus2768.p2769,GridPlus.atNode 2769,GridPlus.atNode 2770,NodePlus43.w17,CompactPlus2768.checked2769,CompactPlus2768.small2769,CompactPlus2768.nodes2769,NodePlus43.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus2768.p2770,GridPlus.atNode 2770,GridPlus.atNode 2771,NodePlus43.w18,CompactPlus2768.checked2770,CompactPlus2768.small2770,CompactPlus2768.nodes2770,NodePlus43.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus2768.p2771,GridPlus.atNode 2771,GridPlus.atNode 2772,NodePlus43.w19,CompactPlus2768.checked2771,CompactPlus2768.small2771,CompactPlus2768.nodes2771,NodePlus43.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus2768.p2772,GridPlus.atNode 2772,GridPlus.atNode 2773,NodePlus43.w20,CompactPlus2768.checked2772,CompactPlus2768.small2772,CompactPlus2768.nodes2772,NodePlus43.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus2768.p2773,GridPlus.atNode 2773,GridPlus.atNode 2774,NodePlus43.w21,CompactPlus2768.checked2773,CompactPlus2768.small2773,CompactPlus2768.nodes2773,NodePlus43.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus2768.p2774,GridPlus.atNode 2774,GridPlus.atNode 2775,NodePlus43.w22,CompactPlus2768.checked2774,CompactPlus2768.small2774,CompactPlus2768.nodes2774,NodePlus43.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus2768.p2775,GridPlus.atNode 2775,GridPlus.atNode 2776,NodePlus43.w23,CompactPlus2768.checked2775,CompactPlus2768.small2775,CompactPlus2768.nodes2775,NodePlus43.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus2768.p2776,GridPlus.atNode 2776,GridPlus.atNode 2777,NodePlus43.w24,CompactPlus2768.checked2776,CompactPlus2768.small2776,CompactPlus2768.nodes2776,NodePlus43.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus2768.p2777,GridPlus.atNode 2777,GridPlus.atNode 2778,NodePlus43.w25,CompactPlus2768.checked2777,CompactPlus2768.small2777,CompactPlus2768.nodes2777,NodePlus43.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus2768.p2778,GridPlus.atNode 2778,GridPlus.atNode 2779,NodePlus43.w26,CompactPlus2768.checked2778,CompactPlus2768.small2778,CompactPlus2768.nodes2778,NodePlus43.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus2768.p2779,GridPlus.atNode 2779,GridPlus.atNode 2780,NodePlus43.w27,CompactPlus2768.checked2779,CompactPlus2768.small2779,CompactPlus2768.nodes2779,NodePlus43.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus2768.p2780,GridPlus.atNode 2780,GridPlus.atNode 2781,NodePlus43.w28,CompactPlus2768.checked2780,CompactPlus2768.small2780,CompactPlus2768.nodes2780,NodePlus43.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus2768.p2781,GridPlus.atNode 2781,GridPlus.atNode 2782,NodePlus43.w29,CompactPlus2768.checked2781,CompactPlus2768.small2781,CompactPlus2768.nodes2781,NodePlus43.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus2768.p2782,GridPlus.atNode 2782,GridPlus.atNode 2783,NodePlus43.w30,CompactPlus2768.checked2782,CompactPlus2768.small2782,CompactPlus2768.nodes2782,NodePlus43.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus2768.p2783,GridPlus.atNode 2783,GridPlus.atNode 2784,NodePlus43.w31,CompactPlus2768.checked2783,CompactPlus2768.small2783,CompactPlus2768.nodes2783,NodePlus43.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus2784.p2784,GridPlus.atNode 2784,GridPlus.atNode 2785,NodePlus43.w32,CompactPlus2784.checked2784,CompactPlus2784.small2784,CompactPlus2784.nodes2784,NodePlus43.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus2784.p2785,GridPlus.atNode 2785,GridPlus.atNode 2786,NodePlus43.w33,CompactPlus2784.checked2785,CompactPlus2784.small2785,CompactPlus2784.nodes2785,NodePlus43.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus2784.p2786,GridPlus.atNode 2786,GridPlus.atNode 2787,NodePlus43.w34,CompactPlus2784.checked2786,CompactPlus2784.small2786,CompactPlus2784.nodes2786,NodePlus43.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus2784.p2787,GridPlus.atNode 2787,GridPlus.atNode 2788,NodePlus43.w35,CompactPlus2784.checked2787,CompactPlus2784.small2787,CompactPlus2784.nodes2787,NodePlus43.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus2784.p2788,GridPlus.atNode 2788,GridPlus.atNode 2789,NodePlus43.w36,CompactPlus2784.checked2788,CompactPlus2784.small2788,CompactPlus2784.nodes2788,NodePlus43.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus2784.p2789,GridPlus.atNode 2789,GridPlus.atNode 2790,NodePlus43.w37,CompactPlus2784.checked2789,CompactPlus2784.small2789,CompactPlus2784.nodes2789,NodePlus43.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus2784.p2790,GridPlus.atNode 2790,GridPlus.atNode 2791,NodePlus43.w38,CompactPlus2784.checked2790,CompactPlus2784.small2790,CompactPlus2784.nodes2790,NodePlus43.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus2784.p2791,GridPlus.atNode 2791,GridPlus.atNode 2792,NodePlus43.w39,CompactPlus2784.checked2791,CompactPlus2784.small2791,CompactPlus2784.nodes2791,NodePlus43.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus2784.p2792,GridPlus.atNode 2792,GridPlus.atNode 2793,NodePlus43.w40,CompactPlus2784.checked2792,CompactPlus2784.small2792,CompactPlus2784.nodes2792,NodePlus43.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus2784.p2793,GridPlus.atNode 2793,GridPlus.atNode 2794,NodePlus43.w41,CompactPlus2784.checked2793,CompactPlus2784.small2793,CompactPlus2784.nodes2793,NodePlus43.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus2784.p2794,GridPlus.atNode 2794,GridPlus.atNode 2795,NodePlus43.w42,CompactPlus2784.checked2794,CompactPlus2784.small2794,CompactPlus2784.nodes2794,NodePlus43.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus2784.p2795,GridPlus.atNode 2795,GridPlus.atNode 2796,NodePlus43.w43,CompactPlus2784.checked2795,CompactPlus2784.small2795,CompactPlus2784.nodes2795,NodePlus43.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus2784.p2796,GridPlus.atNode 2796,GridPlus.atNode 2797,NodePlus43.w44,CompactPlus2784.checked2796,CompactPlus2784.small2796,CompactPlus2784.nodes2796,NodePlus43.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus2784.p2797,GridPlus.atNode 2797,GridPlus.atNode 2798,NodePlus43.w45,CompactPlus2784.checked2797,CompactPlus2784.small2797,CompactPlus2784.nodes2797,NodePlus43.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus2784.p2798,GridPlus.atNode 2798,GridPlus.atNode 2799,NodePlus43.w46,CompactPlus2784.checked2798,CompactPlus2784.small2798,CompactPlus2784.nodes2798,NodePlus43.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus2784.p2799,GridPlus.atNode 2799,GridPlus.atNode 2800,NodePlus43.w47,CompactPlus2784.checked2799,CompactPlus2784.small2799,CompactPlus2784.nodes2799,NodePlus43.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus2800.p2800,GridPlus.atNode 2800,GridPlus.atNode 2801,NodePlus43.w48,CompactPlus2800.checked2800,CompactPlus2800.small2800,CompactPlus2800.nodes2800,NodePlus43.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus2800.p2801,GridPlus.atNode 2801,GridPlus.atNode 2802,NodePlus43.w49,CompactPlus2800.checked2801,CompactPlus2800.small2801,CompactPlus2800.nodes2801,NodePlus43.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus2800.p2802,GridPlus.atNode 2802,GridPlus.atNode 2803,NodePlus43.w50,CompactPlus2800.checked2802,CompactPlus2800.small2802,CompactPlus2800.nodes2802,NodePlus43.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus2800.p2803,GridPlus.atNode 2803,GridPlus.atNode 2804,NodePlus43.w51,CompactPlus2800.checked2803,CompactPlus2800.small2803,CompactPlus2800.nodes2803,NodePlus43.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus2800.p2804,GridPlus.atNode 2804,GridPlus.atNode 2805,NodePlus43.w52,CompactPlus2800.checked2804,CompactPlus2800.small2804,CompactPlus2800.nodes2804,NodePlus43.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus2800.p2805,GridPlus.atNode 2805,GridPlus.atNode 2806,NodePlus43.w53,CompactPlus2800.checked2805,CompactPlus2800.small2805,CompactPlus2800.nodes2805,NodePlus43.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus2800.p2806,GridPlus.atNode 2806,GridPlus.atNode 2807,NodePlus43.w54,CompactPlus2800.checked2806,CompactPlus2800.small2806,CompactPlus2800.nodes2806,NodePlus43.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus2800.p2807,GridPlus.atNode 2807,GridPlus.atNode 2808,NodePlus43.w55,CompactPlus2800.checked2807,CompactPlus2800.small2807,CompactPlus2800.nodes2807,NodePlus43.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus2800.p2808,GridPlus.atNode 2808,GridPlus.atNode 2809,NodePlus43.w56,CompactPlus2800.checked2808,CompactPlus2800.small2808,CompactPlus2800.nodes2808,NodePlus43.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus2800.p2809,GridPlus.atNode 2809,GridPlus.atNode 2810,NodePlus43.w57,CompactPlus2800.checked2809,CompactPlus2800.small2809,CompactPlus2800.nodes2809,NodePlus43.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus2800.p2810,GridPlus.atNode 2810,GridPlus.atNode 2811,NodePlus43.w58,CompactPlus2800.checked2810,CompactPlus2800.small2810,CompactPlus2800.nodes2810,NodePlus43.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus2800.p2811,GridPlus.atNode 2811,GridPlus.atNode 2812,NodePlus43.w59,CompactPlus2800.checked2811,CompactPlus2800.small2811,CompactPlus2800.nodes2811,NodePlus43.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus2800.p2812,GridPlus.atNode 2812,GridPlus.atNode 2813,NodePlus43.w60,CompactPlus2800.checked2812,CompactPlus2800.small2812,CompactPlus2800.nodes2812,NodePlus43.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus2800.p2813,GridPlus.atNode 2813,GridPlus.atNode 2814,NodePlus43.w61,CompactPlus2800.checked2813,CompactPlus2800.small2813,CompactPlus2800.nodes2813,NodePlus43.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus2800.p2814,GridPlus.atNode 2814,GridPlus.atNode 2815,NodePlus43.w62,CompactPlus2800.checked2814,CompactPlus2800.small2814,CompactPlus2800.nodes2814,NodePlus43.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus2800.p2815,GridPlus.atNode 2815,GridPlus.atNode 2816,NodePlus43.w63,CompactPlus2800.checked2815,CompactPlus2800.small2815,CompactPlus2800.nodes2815,NodePlus43.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (2752+j) ∧
    (atRow j).right=GridPlus.atNode (2752+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus43
