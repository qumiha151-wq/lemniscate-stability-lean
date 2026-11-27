import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus2816
import SolitonClassification.Rotating.ResetPackedPlus2832
import SolitonClassification.Rotating.ResetPackedPlus2848
import SolitonClassification.Rotating.ResetPackedPlus2864
namespace SolitonClassification.Rotating.DyadicReset.TilePlus44
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus2816.p2816,GridPlus.atNode 2816,GridPlus.atNode 2817,NodePlus44.w0,CompactPlus2816.checked2816,CompactPlus2816.small2816,CompactPlus2816.nodes2816,NodePlus44.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus2816.p2817,GridPlus.atNode 2817,GridPlus.atNode 2818,NodePlus44.w1,CompactPlus2816.checked2817,CompactPlus2816.small2817,CompactPlus2816.nodes2817,NodePlus44.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus2816.p2818,GridPlus.atNode 2818,GridPlus.atNode 2819,NodePlus44.w2,CompactPlus2816.checked2818,CompactPlus2816.small2818,CompactPlus2816.nodes2818,NodePlus44.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus2816.p2819,GridPlus.atNode 2819,GridPlus.atNode 2820,NodePlus44.w3,CompactPlus2816.checked2819,CompactPlus2816.small2819,CompactPlus2816.nodes2819,NodePlus44.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus2816.p2820,GridPlus.atNode 2820,GridPlus.atNode 2821,NodePlus44.w4,CompactPlus2816.checked2820,CompactPlus2816.small2820,CompactPlus2816.nodes2820,NodePlus44.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus2816.p2821,GridPlus.atNode 2821,GridPlus.atNode 2822,NodePlus44.w5,CompactPlus2816.checked2821,CompactPlus2816.small2821,CompactPlus2816.nodes2821,NodePlus44.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus2816.p2822,GridPlus.atNode 2822,GridPlus.atNode 2823,NodePlus44.w6,CompactPlus2816.checked2822,CompactPlus2816.small2822,CompactPlus2816.nodes2822,NodePlus44.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus2816.p2823,GridPlus.atNode 2823,GridPlus.atNode 2824,NodePlus44.w7,CompactPlus2816.checked2823,CompactPlus2816.small2823,CompactPlus2816.nodes2823,NodePlus44.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus2816.p2824,GridPlus.atNode 2824,GridPlus.atNode 2825,NodePlus44.w8,CompactPlus2816.checked2824,CompactPlus2816.small2824,CompactPlus2816.nodes2824,NodePlus44.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus2816.p2825,GridPlus.atNode 2825,GridPlus.atNode 2826,NodePlus44.w9,CompactPlus2816.checked2825,CompactPlus2816.small2825,CompactPlus2816.nodes2825,NodePlus44.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus2816.p2826,GridPlus.atNode 2826,GridPlus.atNode 2827,NodePlus44.w10,CompactPlus2816.checked2826,CompactPlus2816.small2826,CompactPlus2816.nodes2826,NodePlus44.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus2816.p2827,GridPlus.atNode 2827,GridPlus.atNode 2828,NodePlus44.w11,CompactPlus2816.checked2827,CompactPlus2816.small2827,CompactPlus2816.nodes2827,NodePlus44.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus2816.p2828,GridPlus.atNode 2828,GridPlus.atNode 2829,NodePlus44.w12,CompactPlus2816.checked2828,CompactPlus2816.small2828,CompactPlus2816.nodes2828,NodePlus44.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus2816.p2829,GridPlus.atNode 2829,GridPlus.atNode 2830,NodePlus44.w13,CompactPlus2816.checked2829,CompactPlus2816.small2829,CompactPlus2816.nodes2829,NodePlus44.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus2816.p2830,GridPlus.atNode 2830,GridPlus.atNode 2831,NodePlus44.w14,CompactPlus2816.checked2830,CompactPlus2816.small2830,CompactPlus2816.nodes2830,NodePlus44.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus2816.p2831,GridPlus.atNode 2831,GridPlus.atNode 2832,NodePlus44.w15,CompactPlus2816.checked2831,CompactPlus2816.small2831,CompactPlus2816.nodes2831,NodePlus44.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus2832.p2832,GridPlus.atNode 2832,GridPlus.atNode 2833,NodePlus44.w16,CompactPlus2832.checked2832,CompactPlus2832.small2832,CompactPlus2832.nodes2832,NodePlus44.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus2832.p2833,GridPlus.atNode 2833,GridPlus.atNode 2834,NodePlus44.w17,CompactPlus2832.checked2833,CompactPlus2832.small2833,CompactPlus2832.nodes2833,NodePlus44.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus2832.p2834,GridPlus.atNode 2834,GridPlus.atNode 2835,NodePlus44.w18,CompactPlus2832.checked2834,CompactPlus2832.small2834,CompactPlus2832.nodes2834,NodePlus44.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus2832.p2835,GridPlus.atNode 2835,GridPlus.atNode 2836,NodePlus44.w19,CompactPlus2832.checked2835,CompactPlus2832.small2835,CompactPlus2832.nodes2835,NodePlus44.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus2832.p2836,GridPlus.atNode 2836,GridPlus.atNode 2837,NodePlus44.w20,CompactPlus2832.checked2836,CompactPlus2832.small2836,CompactPlus2832.nodes2836,NodePlus44.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus2832.p2837,GridPlus.atNode 2837,GridPlus.atNode 2838,NodePlus44.w21,CompactPlus2832.checked2837,CompactPlus2832.small2837,CompactPlus2832.nodes2837,NodePlus44.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus2832.p2838,GridPlus.atNode 2838,GridPlus.atNode 2839,NodePlus44.w22,CompactPlus2832.checked2838,CompactPlus2832.small2838,CompactPlus2832.nodes2838,NodePlus44.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus2832.p2839,GridPlus.atNode 2839,GridPlus.atNode 2840,NodePlus44.w23,CompactPlus2832.checked2839,CompactPlus2832.small2839,CompactPlus2832.nodes2839,NodePlus44.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus2832.p2840,GridPlus.atNode 2840,GridPlus.atNode 2841,NodePlus44.w24,CompactPlus2832.checked2840,CompactPlus2832.small2840,CompactPlus2832.nodes2840,NodePlus44.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus2832.p2841,GridPlus.atNode 2841,GridPlus.atNode 2842,NodePlus44.w25,CompactPlus2832.checked2841,CompactPlus2832.small2841,CompactPlus2832.nodes2841,NodePlus44.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus2832.p2842,GridPlus.atNode 2842,GridPlus.atNode 2843,NodePlus44.w26,CompactPlus2832.checked2842,CompactPlus2832.small2842,CompactPlus2832.nodes2842,NodePlus44.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus2832.p2843,GridPlus.atNode 2843,GridPlus.atNode 2844,NodePlus44.w27,CompactPlus2832.checked2843,CompactPlus2832.small2843,CompactPlus2832.nodes2843,NodePlus44.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus2832.p2844,GridPlus.atNode 2844,GridPlus.atNode 2845,NodePlus44.w28,CompactPlus2832.checked2844,CompactPlus2832.small2844,CompactPlus2832.nodes2844,NodePlus44.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus2832.p2845,GridPlus.atNode 2845,GridPlus.atNode 2846,NodePlus44.w29,CompactPlus2832.checked2845,CompactPlus2832.small2845,CompactPlus2832.nodes2845,NodePlus44.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus2832.p2846,GridPlus.atNode 2846,GridPlus.atNode 2847,NodePlus44.w30,CompactPlus2832.checked2846,CompactPlus2832.small2846,CompactPlus2832.nodes2846,NodePlus44.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus2832.p2847,GridPlus.atNode 2847,GridPlus.atNode 2848,NodePlus44.w31,CompactPlus2832.checked2847,CompactPlus2832.small2847,CompactPlus2832.nodes2847,NodePlus44.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus2848.p2848,GridPlus.atNode 2848,GridPlus.atNode 2849,NodePlus44.w32,CompactPlus2848.checked2848,CompactPlus2848.small2848,CompactPlus2848.nodes2848,NodePlus44.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus2848.p2849,GridPlus.atNode 2849,GridPlus.atNode 2850,NodePlus44.w33,CompactPlus2848.checked2849,CompactPlus2848.small2849,CompactPlus2848.nodes2849,NodePlus44.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus2848.p2850,GridPlus.atNode 2850,GridPlus.atNode 2851,NodePlus44.w34,CompactPlus2848.checked2850,CompactPlus2848.small2850,CompactPlus2848.nodes2850,NodePlus44.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus2848.p2851,GridPlus.atNode 2851,GridPlus.atNode 2852,NodePlus44.w35,CompactPlus2848.checked2851,CompactPlus2848.small2851,CompactPlus2848.nodes2851,NodePlus44.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus2848.p2852,GridPlus.atNode 2852,GridPlus.atNode 2853,NodePlus44.w36,CompactPlus2848.checked2852,CompactPlus2848.small2852,CompactPlus2848.nodes2852,NodePlus44.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus2848.p2853,GridPlus.atNode 2853,GridPlus.atNode 2854,NodePlus44.w37,CompactPlus2848.checked2853,CompactPlus2848.small2853,CompactPlus2848.nodes2853,NodePlus44.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus2848.p2854,GridPlus.atNode 2854,GridPlus.atNode 2855,NodePlus44.w38,CompactPlus2848.checked2854,CompactPlus2848.small2854,CompactPlus2848.nodes2854,NodePlus44.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus2848.p2855,GridPlus.atNode 2855,GridPlus.atNode 2856,NodePlus44.w39,CompactPlus2848.checked2855,CompactPlus2848.small2855,CompactPlus2848.nodes2855,NodePlus44.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus2848.p2856,GridPlus.atNode 2856,GridPlus.atNode 2857,NodePlus44.w40,CompactPlus2848.checked2856,CompactPlus2848.small2856,CompactPlus2848.nodes2856,NodePlus44.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus2848.p2857,GridPlus.atNode 2857,GridPlus.atNode 2858,NodePlus44.w41,CompactPlus2848.checked2857,CompactPlus2848.small2857,CompactPlus2848.nodes2857,NodePlus44.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus2848.p2858,GridPlus.atNode 2858,GridPlus.atNode 2859,NodePlus44.w42,CompactPlus2848.checked2858,CompactPlus2848.small2858,CompactPlus2848.nodes2858,NodePlus44.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus2848.p2859,GridPlus.atNode 2859,GridPlus.atNode 2860,NodePlus44.w43,CompactPlus2848.checked2859,CompactPlus2848.small2859,CompactPlus2848.nodes2859,NodePlus44.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus2848.p2860,GridPlus.atNode 2860,GridPlus.atNode 2861,NodePlus44.w44,CompactPlus2848.checked2860,CompactPlus2848.small2860,CompactPlus2848.nodes2860,NodePlus44.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus2848.p2861,GridPlus.atNode 2861,GridPlus.atNode 2862,NodePlus44.w45,CompactPlus2848.checked2861,CompactPlus2848.small2861,CompactPlus2848.nodes2861,NodePlus44.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus2848.p2862,GridPlus.atNode 2862,GridPlus.atNode 2863,NodePlus44.w46,CompactPlus2848.checked2862,CompactPlus2848.small2862,CompactPlus2848.nodes2862,NodePlus44.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus2848.p2863,GridPlus.atNode 2863,GridPlus.atNode 2864,NodePlus44.w47,CompactPlus2848.checked2863,CompactPlus2848.small2863,CompactPlus2848.nodes2863,NodePlus44.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus2864.p2864,GridPlus.atNode 2864,GridPlus.atNode 2865,NodePlus44.w48,CompactPlus2864.checked2864,CompactPlus2864.small2864,CompactPlus2864.nodes2864,NodePlus44.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus2864.p2865,GridPlus.atNode 2865,GridPlus.atNode 2866,NodePlus44.w49,CompactPlus2864.checked2865,CompactPlus2864.small2865,CompactPlus2864.nodes2865,NodePlus44.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus2864.p2866,GridPlus.atNode 2866,GridPlus.atNode 2867,NodePlus44.w50,CompactPlus2864.checked2866,CompactPlus2864.small2866,CompactPlus2864.nodes2866,NodePlus44.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus2864.p2867,GridPlus.atNode 2867,GridPlus.atNode 2868,NodePlus44.w51,CompactPlus2864.checked2867,CompactPlus2864.small2867,CompactPlus2864.nodes2867,NodePlus44.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus2864.p2868,GridPlus.atNode 2868,GridPlus.atNode 2869,NodePlus44.w52,CompactPlus2864.checked2868,CompactPlus2864.small2868,CompactPlus2864.nodes2868,NodePlus44.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus2864.p2869,GridPlus.atNode 2869,GridPlus.atNode 2870,NodePlus44.w53,CompactPlus2864.checked2869,CompactPlus2864.small2869,CompactPlus2864.nodes2869,NodePlus44.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus2864.p2870,GridPlus.atNode 2870,GridPlus.atNode 2871,NodePlus44.w54,CompactPlus2864.checked2870,CompactPlus2864.small2870,CompactPlus2864.nodes2870,NodePlus44.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus2864.p2871,GridPlus.atNode 2871,GridPlus.atNode 2872,NodePlus44.w55,CompactPlus2864.checked2871,CompactPlus2864.small2871,CompactPlus2864.nodes2871,NodePlus44.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus2864.p2872,GridPlus.atNode 2872,GridPlus.atNode 2873,NodePlus44.w56,CompactPlus2864.checked2872,CompactPlus2864.small2872,CompactPlus2864.nodes2872,NodePlus44.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus2864.p2873,GridPlus.atNode 2873,GridPlus.atNode 2874,NodePlus44.w57,CompactPlus2864.checked2873,CompactPlus2864.small2873,CompactPlus2864.nodes2873,NodePlus44.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus2864.p2874,GridPlus.atNode 2874,GridPlus.atNode 2875,NodePlus44.w58,CompactPlus2864.checked2874,CompactPlus2864.small2874,CompactPlus2864.nodes2874,NodePlus44.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus2864.p2875,GridPlus.atNode 2875,GridPlus.atNode 2876,NodePlus44.w59,CompactPlus2864.checked2875,CompactPlus2864.small2875,CompactPlus2864.nodes2875,NodePlus44.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus2864.p2876,GridPlus.atNode 2876,GridPlus.atNode 2877,NodePlus44.w60,CompactPlus2864.checked2876,CompactPlus2864.small2876,CompactPlus2864.nodes2876,NodePlus44.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus2864.p2877,GridPlus.atNode 2877,GridPlus.atNode 2878,NodePlus44.w61,CompactPlus2864.checked2877,CompactPlus2864.small2877,CompactPlus2864.nodes2877,NodePlus44.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus2864.p2878,GridPlus.atNode 2878,GridPlus.atNode 2879,NodePlus44.w62,CompactPlus2864.checked2878,CompactPlus2864.small2878,CompactPlus2864.nodes2878,NodePlus44.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus2864.p2879,GridPlus.atNode 2879,GridPlus.atNode 2880,NodePlus44.w63,CompactPlus2864.checked2879,CompactPlus2864.small2879,CompactPlus2864.nodes2879,NodePlus44.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (2816+j) ∧
    (atRow j).right=GridPlus.atNode (2816+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus44
