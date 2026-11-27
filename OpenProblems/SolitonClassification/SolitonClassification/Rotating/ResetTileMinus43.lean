import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus2752
import SolitonClassification.Rotating.ResetPackedMinus2768
import SolitonClassification.Rotating.ResetPackedMinus2784
import SolitonClassification.Rotating.ResetPackedMinus2800
namespace SolitonClassification.Rotating.DyadicReset.TileMinus43
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2752.p2752,GridMinus.atNode 2752,GridMinus.atNode 2753,NodeMinus43.w0,CompactMinus2752.checked2752,CompactMinus2752.small2752,CompactMinus2752.nodes2752,NodeMinus43.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2752.p2753,GridMinus.atNode 2753,GridMinus.atNode 2754,NodeMinus43.w1,CompactMinus2752.checked2753,CompactMinus2752.small2753,CompactMinus2752.nodes2753,NodeMinus43.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2752.p2754,GridMinus.atNode 2754,GridMinus.atNode 2755,NodeMinus43.w2,CompactMinus2752.checked2754,CompactMinus2752.small2754,CompactMinus2752.nodes2754,NodeMinus43.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2752.p2755,GridMinus.atNode 2755,GridMinus.atNode 2756,NodeMinus43.w3,CompactMinus2752.checked2755,CompactMinus2752.small2755,CompactMinus2752.nodes2755,NodeMinus43.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2752.p2756,GridMinus.atNode 2756,GridMinus.atNode 2757,NodeMinus43.w4,CompactMinus2752.checked2756,CompactMinus2752.small2756,CompactMinus2752.nodes2756,NodeMinus43.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2752.p2757,GridMinus.atNode 2757,GridMinus.atNode 2758,NodeMinus43.w5,CompactMinus2752.checked2757,CompactMinus2752.small2757,CompactMinus2752.nodes2757,NodeMinus43.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2752.p2758,GridMinus.atNode 2758,GridMinus.atNode 2759,NodeMinus43.w6,CompactMinus2752.checked2758,CompactMinus2752.small2758,CompactMinus2752.nodes2758,NodeMinus43.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2752.p2759,GridMinus.atNode 2759,GridMinus.atNode 2760,NodeMinus43.w7,CompactMinus2752.checked2759,CompactMinus2752.small2759,CompactMinus2752.nodes2759,NodeMinus43.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2752.p2760,GridMinus.atNode 2760,GridMinus.atNode 2761,NodeMinus43.w8,CompactMinus2752.checked2760,CompactMinus2752.small2760,CompactMinus2752.nodes2760,NodeMinus43.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2752.p2761,GridMinus.atNode 2761,GridMinus.atNode 2762,NodeMinus43.w9,CompactMinus2752.checked2761,CompactMinus2752.small2761,CompactMinus2752.nodes2761,NodeMinus43.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2752.p2762,GridMinus.atNode 2762,GridMinus.atNode 2763,NodeMinus43.w10,CompactMinus2752.checked2762,CompactMinus2752.small2762,CompactMinus2752.nodes2762,NodeMinus43.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2752.p2763,GridMinus.atNode 2763,GridMinus.atNode 2764,NodeMinus43.w11,CompactMinus2752.checked2763,CompactMinus2752.small2763,CompactMinus2752.nodes2763,NodeMinus43.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2752.p2764,GridMinus.atNode 2764,GridMinus.atNode 2765,NodeMinus43.w12,CompactMinus2752.checked2764,CompactMinus2752.small2764,CompactMinus2752.nodes2764,NodeMinus43.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2752.p2765,GridMinus.atNode 2765,GridMinus.atNode 2766,NodeMinus43.w13,CompactMinus2752.checked2765,CompactMinus2752.small2765,CompactMinus2752.nodes2765,NodeMinus43.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2752.p2766,GridMinus.atNode 2766,GridMinus.atNode 2767,NodeMinus43.w14,CompactMinus2752.checked2766,CompactMinus2752.small2766,CompactMinus2752.nodes2766,NodeMinus43.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2752.p2767,GridMinus.atNode 2767,GridMinus.atNode 2768,NodeMinus43.w15,CompactMinus2752.checked2767,CompactMinus2752.small2767,CompactMinus2752.nodes2767,NodeMinus43.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2768.p2768,GridMinus.atNode 2768,GridMinus.atNode 2769,NodeMinus43.w16,CompactMinus2768.checked2768,CompactMinus2768.small2768,CompactMinus2768.nodes2768,NodeMinus43.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2768.p2769,GridMinus.atNode 2769,GridMinus.atNode 2770,NodeMinus43.w17,CompactMinus2768.checked2769,CompactMinus2768.small2769,CompactMinus2768.nodes2769,NodeMinus43.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2768.p2770,GridMinus.atNode 2770,GridMinus.atNode 2771,NodeMinus43.w18,CompactMinus2768.checked2770,CompactMinus2768.small2770,CompactMinus2768.nodes2770,NodeMinus43.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2768.p2771,GridMinus.atNode 2771,GridMinus.atNode 2772,NodeMinus43.w19,CompactMinus2768.checked2771,CompactMinus2768.small2771,CompactMinus2768.nodes2771,NodeMinus43.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2768.p2772,GridMinus.atNode 2772,GridMinus.atNode 2773,NodeMinus43.w20,CompactMinus2768.checked2772,CompactMinus2768.small2772,CompactMinus2768.nodes2772,NodeMinus43.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2768.p2773,GridMinus.atNode 2773,GridMinus.atNode 2774,NodeMinus43.w21,CompactMinus2768.checked2773,CompactMinus2768.small2773,CompactMinus2768.nodes2773,NodeMinus43.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2768.p2774,GridMinus.atNode 2774,GridMinus.atNode 2775,NodeMinus43.w22,CompactMinus2768.checked2774,CompactMinus2768.small2774,CompactMinus2768.nodes2774,NodeMinus43.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2768.p2775,GridMinus.atNode 2775,GridMinus.atNode 2776,NodeMinus43.w23,CompactMinus2768.checked2775,CompactMinus2768.small2775,CompactMinus2768.nodes2775,NodeMinus43.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2768.p2776,GridMinus.atNode 2776,GridMinus.atNode 2777,NodeMinus43.w24,CompactMinus2768.checked2776,CompactMinus2768.small2776,CompactMinus2768.nodes2776,NodeMinus43.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2768.p2777,GridMinus.atNode 2777,GridMinus.atNode 2778,NodeMinus43.w25,CompactMinus2768.checked2777,CompactMinus2768.small2777,CompactMinus2768.nodes2777,NodeMinus43.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2768.p2778,GridMinus.atNode 2778,GridMinus.atNode 2779,NodeMinus43.w26,CompactMinus2768.checked2778,CompactMinus2768.small2778,CompactMinus2768.nodes2778,NodeMinus43.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2768.p2779,GridMinus.atNode 2779,GridMinus.atNode 2780,NodeMinus43.w27,CompactMinus2768.checked2779,CompactMinus2768.small2779,CompactMinus2768.nodes2779,NodeMinus43.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2768.p2780,GridMinus.atNode 2780,GridMinus.atNode 2781,NodeMinus43.w28,CompactMinus2768.checked2780,CompactMinus2768.small2780,CompactMinus2768.nodes2780,NodeMinus43.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2768.p2781,GridMinus.atNode 2781,GridMinus.atNode 2782,NodeMinus43.w29,CompactMinus2768.checked2781,CompactMinus2768.small2781,CompactMinus2768.nodes2781,NodeMinus43.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2768.p2782,GridMinus.atNode 2782,GridMinus.atNode 2783,NodeMinus43.w30,CompactMinus2768.checked2782,CompactMinus2768.small2782,CompactMinus2768.nodes2782,NodeMinus43.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2768.p2783,GridMinus.atNode 2783,GridMinus.atNode 2784,NodeMinus43.w31,CompactMinus2768.checked2783,CompactMinus2768.small2783,CompactMinus2768.nodes2783,NodeMinus43.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2784.p2784,GridMinus.atNode 2784,GridMinus.atNode 2785,NodeMinus43.w32,CompactMinus2784.checked2784,CompactMinus2784.small2784,CompactMinus2784.nodes2784,NodeMinus43.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2784.p2785,GridMinus.atNode 2785,GridMinus.atNode 2786,NodeMinus43.w33,CompactMinus2784.checked2785,CompactMinus2784.small2785,CompactMinus2784.nodes2785,NodeMinus43.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2784.p2786,GridMinus.atNode 2786,GridMinus.atNode 2787,NodeMinus43.w34,CompactMinus2784.checked2786,CompactMinus2784.small2786,CompactMinus2784.nodes2786,NodeMinus43.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2784.p2787,GridMinus.atNode 2787,GridMinus.atNode 2788,NodeMinus43.w35,CompactMinus2784.checked2787,CompactMinus2784.small2787,CompactMinus2784.nodes2787,NodeMinus43.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2784.p2788,GridMinus.atNode 2788,GridMinus.atNode 2789,NodeMinus43.w36,CompactMinus2784.checked2788,CompactMinus2784.small2788,CompactMinus2784.nodes2788,NodeMinus43.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2784.p2789,GridMinus.atNode 2789,GridMinus.atNode 2790,NodeMinus43.w37,CompactMinus2784.checked2789,CompactMinus2784.small2789,CompactMinus2784.nodes2789,NodeMinus43.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2784.p2790,GridMinus.atNode 2790,GridMinus.atNode 2791,NodeMinus43.w38,CompactMinus2784.checked2790,CompactMinus2784.small2790,CompactMinus2784.nodes2790,NodeMinus43.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2784.p2791,GridMinus.atNode 2791,GridMinus.atNode 2792,NodeMinus43.w39,CompactMinus2784.checked2791,CompactMinus2784.small2791,CompactMinus2784.nodes2791,NodeMinus43.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2784.p2792,GridMinus.atNode 2792,GridMinus.atNode 2793,NodeMinus43.w40,CompactMinus2784.checked2792,CompactMinus2784.small2792,CompactMinus2784.nodes2792,NodeMinus43.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2784.p2793,GridMinus.atNode 2793,GridMinus.atNode 2794,NodeMinus43.w41,CompactMinus2784.checked2793,CompactMinus2784.small2793,CompactMinus2784.nodes2793,NodeMinus43.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2784.p2794,GridMinus.atNode 2794,GridMinus.atNode 2795,NodeMinus43.w42,CompactMinus2784.checked2794,CompactMinus2784.small2794,CompactMinus2784.nodes2794,NodeMinus43.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2784.p2795,GridMinus.atNode 2795,GridMinus.atNode 2796,NodeMinus43.w43,CompactMinus2784.checked2795,CompactMinus2784.small2795,CompactMinus2784.nodes2795,NodeMinus43.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2784.p2796,GridMinus.atNode 2796,GridMinus.atNode 2797,NodeMinus43.w44,CompactMinus2784.checked2796,CompactMinus2784.small2796,CompactMinus2784.nodes2796,NodeMinus43.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2784.p2797,GridMinus.atNode 2797,GridMinus.atNode 2798,NodeMinus43.w45,CompactMinus2784.checked2797,CompactMinus2784.small2797,CompactMinus2784.nodes2797,NodeMinus43.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2784.p2798,GridMinus.atNode 2798,GridMinus.atNode 2799,NodeMinus43.w46,CompactMinus2784.checked2798,CompactMinus2784.small2798,CompactMinus2784.nodes2798,NodeMinus43.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2784.p2799,GridMinus.atNode 2799,GridMinus.atNode 2800,NodeMinus43.w47,CompactMinus2784.checked2799,CompactMinus2784.small2799,CompactMinus2784.nodes2799,NodeMinus43.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2800.p2800,GridMinus.atNode 2800,GridMinus.atNode 2801,NodeMinus43.w48,CompactMinus2800.checked2800,CompactMinus2800.small2800,CompactMinus2800.nodes2800,NodeMinus43.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2800.p2801,GridMinus.atNode 2801,GridMinus.atNode 2802,NodeMinus43.w49,CompactMinus2800.checked2801,CompactMinus2800.small2801,CompactMinus2800.nodes2801,NodeMinus43.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2800.p2802,GridMinus.atNode 2802,GridMinus.atNode 2803,NodeMinus43.w50,CompactMinus2800.checked2802,CompactMinus2800.small2802,CompactMinus2800.nodes2802,NodeMinus43.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2800.p2803,GridMinus.atNode 2803,GridMinus.atNode 2804,NodeMinus43.w51,CompactMinus2800.checked2803,CompactMinus2800.small2803,CompactMinus2800.nodes2803,NodeMinus43.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2800.p2804,GridMinus.atNode 2804,GridMinus.atNode 2805,NodeMinus43.w52,CompactMinus2800.checked2804,CompactMinus2800.small2804,CompactMinus2800.nodes2804,NodeMinus43.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2800.p2805,GridMinus.atNode 2805,GridMinus.atNode 2806,NodeMinus43.w53,CompactMinus2800.checked2805,CompactMinus2800.small2805,CompactMinus2800.nodes2805,NodeMinus43.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2800.p2806,GridMinus.atNode 2806,GridMinus.atNode 2807,NodeMinus43.w54,CompactMinus2800.checked2806,CompactMinus2800.small2806,CompactMinus2800.nodes2806,NodeMinus43.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2800.p2807,GridMinus.atNode 2807,GridMinus.atNode 2808,NodeMinus43.w55,CompactMinus2800.checked2807,CompactMinus2800.small2807,CompactMinus2800.nodes2807,NodeMinus43.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2800.p2808,GridMinus.atNode 2808,GridMinus.atNode 2809,NodeMinus43.w56,CompactMinus2800.checked2808,CompactMinus2800.small2808,CompactMinus2800.nodes2808,NodeMinus43.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2800.p2809,GridMinus.atNode 2809,GridMinus.atNode 2810,NodeMinus43.w57,CompactMinus2800.checked2809,CompactMinus2800.small2809,CompactMinus2800.nodes2809,NodeMinus43.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2800.p2810,GridMinus.atNode 2810,GridMinus.atNode 2811,NodeMinus43.w58,CompactMinus2800.checked2810,CompactMinus2800.small2810,CompactMinus2800.nodes2810,NodeMinus43.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2800.p2811,GridMinus.atNode 2811,GridMinus.atNode 2812,NodeMinus43.w59,CompactMinus2800.checked2811,CompactMinus2800.small2811,CompactMinus2800.nodes2811,NodeMinus43.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2800.p2812,GridMinus.atNode 2812,GridMinus.atNode 2813,NodeMinus43.w60,CompactMinus2800.checked2812,CompactMinus2800.small2812,CompactMinus2800.nodes2812,NodeMinus43.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2800.p2813,GridMinus.atNode 2813,GridMinus.atNode 2814,NodeMinus43.w61,CompactMinus2800.checked2813,CompactMinus2800.small2813,CompactMinus2800.nodes2813,NodeMinus43.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2800.p2814,GridMinus.atNode 2814,GridMinus.atNode 2815,NodeMinus43.w62,CompactMinus2800.checked2814,CompactMinus2800.small2814,CompactMinus2800.nodes2814,NodeMinus43.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2800.p2815,GridMinus.atNode 2815,GridMinus.atNode 2816,NodeMinus43.w63,CompactMinus2800.checked2815,CompactMinus2800.small2815,CompactMinus2800.nodes2815,NodeMinus43.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (2752+j) ∧
    (atRow j).right=GridMinus.atNode (2752+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus43
