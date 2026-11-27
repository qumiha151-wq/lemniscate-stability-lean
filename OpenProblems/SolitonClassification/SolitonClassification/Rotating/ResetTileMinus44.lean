import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus2816
import SolitonClassification.Rotating.ResetPackedMinus2832
import SolitonClassification.Rotating.ResetPackedMinus2848
import SolitonClassification.Rotating.ResetPackedMinus2864
namespace SolitonClassification.Rotating.DyadicReset.TileMinus44
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2816.p2816,GridMinus.atNode 2816,GridMinus.atNode 2817,NodeMinus44.w0,CompactMinus2816.checked2816,CompactMinus2816.small2816,CompactMinus2816.nodes2816,NodeMinus44.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2816.p2817,GridMinus.atNode 2817,GridMinus.atNode 2818,NodeMinus44.w1,CompactMinus2816.checked2817,CompactMinus2816.small2817,CompactMinus2816.nodes2817,NodeMinus44.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2816.p2818,GridMinus.atNode 2818,GridMinus.atNode 2819,NodeMinus44.w2,CompactMinus2816.checked2818,CompactMinus2816.small2818,CompactMinus2816.nodes2818,NodeMinus44.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2816.p2819,GridMinus.atNode 2819,GridMinus.atNode 2820,NodeMinus44.w3,CompactMinus2816.checked2819,CompactMinus2816.small2819,CompactMinus2816.nodes2819,NodeMinus44.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2816.p2820,GridMinus.atNode 2820,GridMinus.atNode 2821,NodeMinus44.w4,CompactMinus2816.checked2820,CompactMinus2816.small2820,CompactMinus2816.nodes2820,NodeMinus44.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2816.p2821,GridMinus.atNode 2821,GridMinus.atNode 2822,NodeMinus44.w5,CompactMinus2816.checked2821,CompactMinus2816.small2821,CompactMinus2816.nodes2821,NodeMinus44.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2816.p2822,GridMinus.atNode 2822,GridMinus.atNode 2823,NodeMinus44.w6,CompactMinus2816.checked2822,CompactMinus2816.small2822,CompactMinus2816.nodes2822,NodeMinus44.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2816.p2823,GridMinus.atNode 2823,GridMinus.atNode 2824,NodeMinus44.w7,CompactMinus2816.checked2823,CompactMinus2816.small2823,CompactMinus2816.nodes2823,NodeMinus44.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2816.p2824,GridMinus.atNode 2824,GridMinus.atNode 2825,NodeMinus44.w8,CompactMinus2816.checked2824,CompactMinus2816.small2824,CompactMinus2816.nodes2824,NodeMinus44.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2816.p2825,GridMinus.atNode 2825,GridMinus.atNode 2826,NodeMinus44.w9,CompactMinus2816.checked2825,CompactMinus2816.small2825,CompactMinus2816.nodes2825,NodeMinus44.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2816.p2826,GridMinus.atNode 2826,GridMinus.atNode 2827,NodeMinus44.w10,CompactMinus2816.checked2826,CompactMinus2816.small2826,CompactMinus2816.nodes2826,NodeMinus44.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2816.p2827,GridMinus.atNode 2827,GridMinus.atNode 2828,NodeMinus44.w11,CompactMinus2816.checked2827,CompactMinus2816.small2827,CompactMinus2816.nodes2827,NodeMinus44.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2816.p2828,GridMinus.atNode 2828,GridMinus.atNode 2829,NodeMinus44.w12,CompactMinus2816.checked2828,CompactMinus2816.small2828,CompactMinus2816.nodes2828,NodeMinus44.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2816.p2829,GridMinus.atNode 2829,GridMinus.atNode 2830,NodeMinus44.w13,CompactMinus2816.checked2829,CompactMinus2816.small2829,CompactMinus2816.nodes2829,NodeMinus44.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2816.p2830,GridMinus.atNode 2830,GridMinus.atNode 2831,NodeMinus44.w14,CompactMinus2816.checked2830,CompactMinus2816.small2830,CompactMinus2816.nodes2830,NodeMinus44.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2816.p2831,GridMinus.atNode 2831,GridMinus.atNode 2832,NodeMinus44.w15,CompactMinus2816.checked2831,CompactMinus2816.small2831,CompactMinus2816.nodes2831,NodeMinus44.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2832.p2832,GridMinus.atNode 2832,GridMinus.atNode 2833,NodeMinus44.w16,CompactMinus2832.checked2832,CompactMinus2832.small2832,CompactMinus2832.nodes2832,NodeMinus44.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2832.p2833,GridMinus.atNode 2833,GridMinus.atNode 2834,NodeMinus44.w17,CompactMinus2832.checked2833,CompactMinus2832.small2833,CompactMinus2832.nodes2833,NodeMinus44.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2832.p2834,GridMinus.atNode 2834,GridMinus.atNode 2835,NodeMinus44.w18,CompactMinus2832.checked2834,CompactMinus2832.small2834,CompactMinus2832.nodes2834,NodeMinus44.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2832.p2835,GridMinus.atNode 2835,GridMinus.atNode 2836,NodeMinus44.w19,CompactMinus2832.checked2835,CompactMinus2832.small2835,CompactMinus2832.nodes2835,NodeMinus44.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2832.p2836,GridMinus.atNode 2836,GridMinus.atNode 2837,NodeMinus44.w20,CompactMinus2832.checked2836,CompactMinus2832.small2836,CompactMinus2832.nodes2836,NodeMinus44.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2832.p2837,GridMinus.atNode 2837,GridMinus.atNode 2838,NodeMinus44.w21,CompactMinus2832.checked2837,CompactMinus2832.small2837,CompactMinus2832.nodes2837,NodeMinus44.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2832.p2838,GridMinus.atNode 2838,GridMinus.atNode 2839,NodeMinus44.w22,CompactMinus2832.checked2838,CompactMinus2832.small2838,CompactMinus2832.nodes2838,NodeMinus44.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2832.p2839,GridMinus.atNode 2839,GridMinus.atNode 2840,NodeMinus44.w23,CompactMinus2832.checked2839,CompactMinus2832.small2839,CompactMinus2832.nodes2839,NodeMinus44.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2832.p2840,GridMinus.atNode 2840,GridMinus.atNode 2841,NodeMinus44.w24,CompactMinus2832.checked2840,CompactMinus2832.small2840,CompactMinus2832.nodes2840,NodeMinus44.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2832.p2841,GridMinus.atNode 2841,GridMinus.atNode 2842,NodeMinus44.w25,CompactMinus2832.checked2841,CompactMinus2832.small2841,CompactMinus2832.nodes2841,NodeMinus44.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2832.p2842,GridMinus.atNode 2842,GridMinus.atNode 2843,NodeMinus44.w26,CompactMinus2832.checked2842,CompactMinus2832.small2842,CompactMinus2832.nodes2842,NodeMinus44.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2832.p2843,GridMinus.atNode 2843,GridMinus.atNode 2844,NodeMinus44.w27,CompactMinus2832.checked2843,CompactMinus2832.small2843,CompactMinus2832.nodes2843,NodeMinus44.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2832.p2844,GridMinus.atNode 2844,GridMinus.atNode 2845,NodeMinus44.w28,CompactMinus2832.checked2844,CompactMinus2832.small2844,CompactMinus2832.nodes2844,NodeMinus44.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2832.p2845,GridMinus.atNode 2845,GridMinus.atNode 2846,NodeMinus44.w29,CompactMinus2832.checked2845,CompactMinus2832.small2845,CompactMinus2832.nodes2845,NodeMinus44.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2832.p2846,GridMinus.atNode 2846,GridMinus.atNode 2847,NodeMinus44.w30,CompactMinus2832.checked2846,CompactMinus2832.small2846,CompactMinus2832.nodes2846,NodeMinus44.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2832.p2847,GridMinus.atNode 2847,GridMinus.atNode 2848,NodeMinus44.w31,CompactMinus2832.checked2847,CompactMinus2832.small2847,CompactMinus2832.nodes2847,NodeMinus44.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2848.p2848,GridMinus.atNode 2848,GridMinus.atNode 2849,NodeMinus44.w32,CompactMinus2848.checked2848,CompactMinus2848.small2848,CompactMinus2848.nodes2848,NodeMinus44.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2848.p2849,GridMinus.atNode 2849,GridMinus.atNode 2850,NodeMinus44.w33,CompactMinus2848.checked2849,CompactMinus2848.small2849,CompactMinus2848.nodes2849,NodeMinus44.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2848.p2850,GridMinus.atNode 2850,GridMinus.atNode 2851,NodeMinus44.w34,CompactMinus2848.checked2850,CompactMinus2848.small2850,CompactMinus2848.nodes2850,NodeMinus44.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2848.p2851,GridMinus.atNode 2851,GridMinus.atNode 2852,NodeMinus44.w35,CompactMinus2848.checked2851,CompactMinus2848.small2851,CompactMinus2848.nodes2851,NodeMinus44.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2848.p2852,GridMinus.atNode 2852,GridMinus.atNode 2853,NodeMinus44.w36,CompactMinus2848.checked2852,CompactMinus2848.small2852,CompactMinus2848.nodes2852,NodeMinus44.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2848.p2853,GridMinus.atNode 2853,GridMinus.atNode 2854,NodeMinus44.w37,CompactMinus2848.checked2853,CompactMinus2848.small2853,CompactMinus2848.nodes2853,NodeMinus44.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2848.p2854,GridMinus.atNode 2854,GridMinus.atNode 2855,NodeMinus44.w38,CompactMinus2848.checked2854,CompactMinus2848.small2854,CompactMinus2848.nodes2854,NodeMinus44.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2848.p2855,GridMinus.atNode 2855,GridMinus.atNode 2856,NodeMinus44.w39,CompactMinus2848.checked2855,CompactMinus2848.small2855,CompactMinus2848.nodes2855,NodeMinus44.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2848.p2856,GridMinus.atNode 2856,GridMinus.atNode 2857,NodeMinus44.w40,CompactMinus2848.checked2856,CompactMinus2848.small2856,CompactMinus2848.nodes2856,NodeMinus44.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2848.p2857,GridMinus.atNode 2857,GridMinus.atNode 2858,NodeMinus44.w41,CompactMinus2848.checked2857,CompactMinus2848.small2857,CompactMinus2848.nodes2857,NodeMinus44.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2848.p2858,GridMinus.atNode 2858,GridMinus.atNode 2859,NodeMinus44.w42,CompactMinus2848.checked2858,CompactMinus2848.small2858,CompactMinus2848.nodes2858,NodeMinus44.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2848.p2859,GridMinus.atNode 2859,GridMinus.atNode 2860,NodeMinus44.w43,CompactMinus2848.checked2859,CompactMinus2848.small2859,CompactMinus2848.nodes2859,NodeMinus44.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2848.p2860,GridMinus.atNode 2860,GridMinus.atNode 2861,NodeMinus44.w44,CompactMinus2848.checked2860,CompactMinus2848.small2860,CompactMinus2848.nodes2860,NodeMinus44.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2848.p2861,GridMinus.atNode 2861,GridMinus.atNode 2862,NodeMinus44.w45,CompactMinus2848.checked2861,CompactMinus2848.small2861,CompactMinus2848.nodes2861,NodeMinus44.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2848.p2862,GridMinus.atNode 2862,GridMinus.atNode 2863,NodeMinus44.w46,CompactMinus2848.checked2862,CompactMinus2848.small2862,CompactMinus2848.nodes2862,NodeMinus44.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2848.p2863,GridMinus.atNode 2863,GridMinus.atNode 2864,NodeMinus44.w47,CompactMinus2848.checked2863,CompactMinus2848.small2863,CompactMinus2848.nodes2863,NodeMinus44.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2864.p2864,GridMinus.atNode 2864,GridMinus.atNode 2865,NodeMinus44.w48,CompactMinus2864.checked2864,CompactMinus2864.small2864,CompactMinus2864.nodes2864,NodeMinus44.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2864.p2865,GridMinus.atNode 2865,GridMinus.atNode 2866,NodeMinus44.w49,CompactMinus2864.checked2865,CompactMinus2864.small2865,CompactMinus2864.nodes2865,NodeMinus44.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2864.p2866,GridMinus.atNode 2866,GridMinus.atNode 2867,NodeMinus44.w50,CompactMinus2864.checked2866,CompactMinus2864.small2866,CompactMinus2864.nodes2866,NodeMinus44.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2864.p2867,GridMinus.atNode 2867,GridMinus.atNode 2868,NodeMinus44.w51,CompactMinus2864.checked2867,CompactMinus2864.small2867,CompactMinus2864.nodes2867,NodeMinus44.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2864.p2868,GridMinus.atNode 2868,GridMinus.atNode 2869,NodeMinus44.w52,CompactMinus2864.checked2868,CompactMinus2864.small2868,CompactMinus2864.nodes2868,NodeMinus44.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2864.p2869,GridMinus.atNode 2869,GridMinus.atNode 2870,NodeMinus44.w53,CompactMinus2864.checked2869,CompactMinus2864.small2869,CompactMinus2864.nodes2869,NodeMinus44.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2864.p2870,GridMinus.atNode 2870,GridMinus.atNode 2871,NodeMinus44.w54,CompactMinus2864.checked2870,CompactMinus2864.small2870,CompactMinus2864.nodes2870,NodeMinus44.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2864.p2871,GridMinus.atNode 2871,GridMinus.atNode 2872,NodeMinus44.w55,CompactMinus2864.checked2871,CompactMinus2864.small2871,CompactMinus2864.nodes2871,NodeMinus44.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2864.p2872,GridMinus.atNode 2872,GridMinus.atNode 2873,NodeMinus44.w56,CompactMinus2864.checked2872,CompactMinus2864.small2872,CompactMinus2864.nodes2872,NodeMinus44.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2864.p2873,GridMinus.atNode 2873,GridMinus.atNode 2874,NodeMinus44.w57,CompactMinus2864.checked2873,CompactMinus2864.small2873,CompactMinus2864.nodes2873,NodeMinus44.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2864.p2874,GridMinus.atNode 2874,GridMinus.atNode 2875,NodeMinus44.w58,CompactMinus2864.checked2874,CompactMinus2864.small2874,CompactMinus2864.nodes2874,NodeMinus44.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2864.p2875,GridMinus.atNode 2875,GridMinus.atNode 2876,NodeMinus44.w59,CompactMinus2864.checked2875,CompactMinus2864.small2875,CompactMinus2864.nodes2875,NodeMinus44.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2864.p2876,GridMinus.atNode 2876,GridMinus.atNode 2877,NodeMinus44.w60,CompactMinus2864.checked2876,CompactMinus2864.small2876,CompactMinus2864.nodes2876,NodeMinus44.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2864.p2877,GridMinus.atNode 2877,GridMinus.atNode 2878,NodeMinus44.w61,CompactMinus2864.checked2877,CompactMinus2864.small2877,CompactMinus2864.nodes2877,NodeMinus44.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2864.p2878,GridMinus.atNode 2878,GridMinus.atNode 2879,NodeMinus44.w62,CompactMinus2864.checked2878,CompactMinus2864.small2878,CompactMinus2864.nodes2878,NodeMinus44.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2864.p2879,GridMinus.atNode 2879,GridMinus.atNode 2880,NodeMinus44.w63,CompactMinus2864.checked2879,CompactMinus2864.small2879,CompactMinus2864.nodes2879,NodeMinus44.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (2816+j) ∧
    (atRow j).right=GridMinus.atNode (2816+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus44
