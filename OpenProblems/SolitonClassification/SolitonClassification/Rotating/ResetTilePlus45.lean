import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus2880
import SolitonClassification.Rotating.ResetPackedPlus2896
import SolitonClassification.Rotating.ResetPackedPlus2912
import SolitonClassification.Rotating.ResetPackedPlus2928
namespace SolitonClassification.Rotating.DyadicReset.TilePlus45
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus2880.p2880,GridPlus.atNode 2880,GridPlus.atNode 2881,NodePlus45.w0,CompactPlus2880.checked2880,CompactPlus2880.small2880,CompactPlus2880.nodes2880,NodePlus45.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus2880.p2881,GridPlus.atNode 2881,GridPlus.atNode 2882,NodePlus45.w1,CompactPlus2880.checked2881,CompactPlus2880.small2881,CompactPlus2880.nodes2881,NodePlus45.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus2880.p2882,GridPlus.atNode 2882,GridPlus.atNode 2883,NodePlus45.w2,CompactPlus2880.checked2882,CompactPlus2880.small2882,CompactPlus2880.nodes2882,NodePlus45.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus2880.p2883,GridPlus.atNode 2883,GridPlus.atNode 2884,NodePlus45.w3,CompactPlus2880.checked2883,CompactPlus2880.small2883,CompactPlus2880.nodes2883,NodePlus45.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus2880.p2884,GridPlus.atNode 2884,GridPlus.atNode 2885,NodePlus45.w4,CompactPlus2880.checked2884,CompactPlus2880.small2884,CompactPlus2880.nodes2884,NodePlus45.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus2880.p2885,GridPlus.atNode 2885,GridPlus.atNode 2886,NodePlus45.w5,CompactPlus2880.checked2885,CompactPlus2880.small2885,CompactPlus2880.nodes2885,NodePlus45.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus2880.p2886,GridPlus.atNode 2886,GridPlus.atNode 2887,NodePlus45.w6,CompactPlus2880.checked2886,CompactPlus2880.small2886,CompactPlus2880.nodes2886,NodePlus45.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus2880.p2887,GridPlus.atNode 2887,GridPlus.atNode 2888,NodePlus45.w7,CompactPlus2880.checked2887,CompactPlus2880.small2887,CompactPlus2880.nodes2887,NodePlus45.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus2880.p2888,GridPlus.atNode 2888,GridPlus.atNode 2889,NodePlus45.w8,CompactPlus2880.checked2888,CompactPlus2880.small2888,CompactPlus2880.nodes2888,NodePlus45.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus2880.p2889,GridPlus.atNode 2889,GridPlus.atNode 2890,NodePlus45.w9,CompactPlus2880.checked2889,CompactPlus2880.small2889,CompactPlus2880.nodes2889,NodePlus45.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus2880.p2890,GridPlus.atNode 2890,GridPlus.atNode 2891,NodePlus45.w10,CompactPlus2880.checked2890,CompactPlus2880.small2890,CompactPlus2880.nodes2890,NodePlus45.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus2880.p2891,GridPlus.atNode 2891,GridPlus.atNode 2892,NodePlus45.w11,CompactPlus2880.checked2891,CompactPlus2880.small2891,CompactPlus2880.nodes2891,NodePlus45.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus2880.p2892,GridPlus.atNode 2892,GridPlus.atNode 2893,NodePlus45.w12,CompactPlus2880.checked2892,CompactPlus2880.small2892,CompactPlus2880.nodes2892,NodePlus45.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus2880.p2893,GridPlus.atNode 2893,GridPlus.atNode 2894,NodePlus45.w13,CompactPlus2880.checked2893,CompactPlus2880.small2893,CompactPlus2880.nodes2893,NodePlus45.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus2880.p2894,GridPlus.atNode 2894,GridPlus.atNode 2895,NodePlus45.w14,CompactPlus2880.checked2894,CompactPlus2880.small2894,CompactPlus2880.nodes2894,NodePlus45.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus2880.p2895,GridPlus.atNode 2895,GridPlus.atNode 2896,NodePlus45.w15,CompactPlus2880.checked2895,CompactPlus2880.small2895,CompactPlus2880.nodes2895,NodePlus45.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus2896.p2896,GridPlus.atNode 2896,GridPlus.atNode 2897,NodePlus45.w16,CompactPlus2896.checked2896,CompactPlus2896.small2896,CompactPlus2896.nodes2896,NodePlus45.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus2896.p2897,GridPlus.atNode 2897,GridPlus.atNode 2898,NodePlus45.w17,CompactPlus2896.checked2897,CompactPlus2896.small2897,CompactPlus2896.nodes2897,NodePlus45.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus2896.p2898,GridPlus.atNode 2898,GridPlus.atNode 2899,NodePlus45.w18,CompactPlus2896.checked2898,CompactPlus2896.small2898,CompactPlus2896.nodes2898,NodePlus45.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus2896.p2899,GridPlus.atNode 2899,GridPlus.atNode 2900,NodePlus45.w19,CompactPlus2896.checked2899,CompactPlus2896.small2899,CompactPlus2896.nodes2899,NodePlus45.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus2896.p2900,GridPlus.atNode 2900,GridPlus.atNode 2901,NodePlus45.w20,CompactPlus2896.checked2900,CompactPlus2896.small2900,CompactPlus2896.nodes2900,NodePlus45.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus2896.p2901,GridPlus.atNode 2901,GridPlus.atNode 2902,NodePlus45.w21,CompactPlus2896.checked2901,CompactPlus2896.small2901,CompactPlus2896.nodes2901,NodePlus45.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus2896.p2902,GridPlus.atNode 2902,GridPlus.atNode 2903,NodePlus45.w22,CompactPlus2896.checked2902,CompactPlus2896.small2902,CompactPlus2896.nodes2902,NodePlus45.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus2896.p2903,GridPlus.atNode 2903,GridPlus.atNode 2904,NodePlus45.w23,CompactPlus2896.checked2903,CompactPlus2896.small2903,CompactPlus2896.nodes2903,NodePlus45.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus2896.p2904,GridPlus.atNode 2904,GridPlus.atNode 2905,NodePlus45.w24,CompactPlus2896.checked2904,CompactPlus2896.small2904,CompactPlus2896.nodes2904,NodePlus45.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus2896.p2905,GridPlus.atNode 2905,GridPlus.atNode 2906,NodePlus45.w25,CompactPlus2896.checked2905,CompactPlus2896.small2905,CompactPlus2896.nodes2905,NodePlus45.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus2896.p2906,GridPlus.atNode 2906,GridPlus.atNode 2907,NodePlus45.w26,CompactPlus2896.checked2906,CompactPlus2896.small2906,CompactPlus2896.nodes2906,NodePlus45.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus2896.p2907,GridPlus.atNode 2907,GridPlus.atNode 2908,NodePlus45.w27,CompactPlus2896.checked2907,CompactPlus2896.small2907,CompactPlus2896.nodes2907,NodePlus45.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus2896.p2908,GridPlus.atNode 2908,GridPlus.atNode 2909,NodePlus45.w28,CompactPlus2896.checked2908,CompactPlus2896.small2908,CompactPlus2896.nodes2908,NodePlus45.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus2896.p2909,GridPlus.atNode 2909,GridPlus.atNode 2910,NodePlus45.w29,CompactPlus2896.checked2909,CompactPlus2896.small2909,CompactPlus2896.nodes2909,NodePlus45.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus2896.p2910,GridPlus.atNode 2910,GridPlus.atNode 2911,NodePlus45.w30,CompactPlus2896.checked2910,CompactPlus2896.small2910,CompactPlus2896.nodes2910,NodePlus45.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus2896.p2911,GridPlus.atNode 2911,GridPlus.atNode 2912,NodePlus45.w31,CompactPlus2896.checked2911,CompactPlus2896.small2911,CompactPlus2896.nodes2911,NodePlus45.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus2912.p2912,GridPlus.atNode 2912,GridPlus.atNode 2913,NodePlus45.w32,CompactPlus2912.checked2912,CompactPlus2912.small2912,CompactPlus2912.nodes2912,NodePlus45.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus2912.p2913,GridPlus.atNode 2913,GridPlus.atNode 2914,NodePlus45.w33,CompactPlus2912.checked2913,CompactPlus2912.small2913,CompactPlus2912.nodes2913,NodePlus45.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus2912.p2914,GridPlus.atNode 2914,GridPlus.atNode 2915,NodePlus45.w34,CompactPlus2912.checked2914,CompactPlus2912.small2914,CompactPlus2912.nodes2914,NodePlus45.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus2912.p2915,GridPlus.atNode 2915,GridPlus.atNode 2916,NodePlus45.w35,CompactPlus2912.checked2915,CompactPlus2912.small2915,CompactPlus2912.nodes2915,NodePlus45.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus2912.p2916,GridPlus.atNode 2916,GridPlus.atNode 2917,NodePlus45.w36,CompactPlus2912.checked2916,CompactPlus2912.small2916,CompactPlus2912.nodes2916,NodePlus45.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus2912.p2917,GridPlus.atNode 2917,GridPlus.atNode 2918,NodePlus45.w37,CompactPlus2912.checked2917,CompactPlus2912.small2917,CompactPlus2912.nodes2917,NodePlus45.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus2912.p2918,GridPlus.atNode 2918,GridPlus.atNode 2919,NodePlus45.w38,CompactPlus2912.checked2918,CompactPlus2912.small2918,CompactPlus2912.nodes2918,NodePlus45.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus2912.p2919,GridPlus.atNode 2919,GridPlus.atNode 2920,NodePlus45.w39,CompactPlus2912.checked2919,CompactPlus2912.small2919,CompactPlus2912.nodes2919,NodePlus45.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus2912.p2920,GridPlus.atNode 2920,GridPlus.atNode 2921,NodePlus45.w40,CompactPlus2912.checked2920,CompactPlus2912.small2920,CompactPlus2912.nodes2920,NodePlus45.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus2912.p2921,GridPlus.atNode 2921,GridPlus.atNode 2922,NodePlus45.w41,CompactPlus2912.checked2921,CompactPlus2912.small2921,CompactPlus2912.nodes2921,NodePlus45.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus2912.p2922,GridPlus.atNode 2922,GridPlus.atNode 2923,NodePlus45.w42,CompactPlus2912.checked2922,CompactPlus2912.small2922,CompactPlus2912.nodes2922,NodePlus45.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus2912.p2923,GridPlus.atNode 2923,GridPlus.atNode 2924,NodePlus45.w43,CompactPlus2912.checked2923,CompactPlus2912.small2923,CompactPlus2912.nodes2923,NodePlus45.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus2912.p2924,GridPlus.atNode 2924,GridPlus.atNode 2925,NodePlus45.w44,CompactPlus2912.checked2924,CompactPlus2912.small2924,CompactPlus2912.nodes2924,NodePlus45.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus2912.p2925,GridPlus.atNode 2925,GridPlus.atNode 2926,NodePlus45.w45,CompactPlus2912.checked2925,CompactPlus2912.small2925,CompactPlus2912.nodes2925,NodePlus45.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus2912.p2926,GridPlus.atNode 2926,GridPlus.atNode 2927,NodePlus45.w46,CompactPlus2912.checked2926,CompactPlus2912.small2926,CompactPlus2912.nodes2926,NodePlus45.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus2912.p2927,GridPlus.atNode 2927,GridPlus.atNode 2928,NodePlus45.w47,CompactPlus2912.checked2927,CompactPlus2912.small2927,CompactPlus2912.nodes2927,NodePlus45.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus2928.p2928,GridPlus.atNode 2928,GridPlus.atNode 2929,NodePlus45.w48,CompactPlus2928.checked2928,CompactPlus2928.small2928,CompactPlus2928.nodes2928,NodePlus45.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus2928.p2929,GridPlus.atNode 2929,GridPlus.atNode 2930,NodePlus45.w49,CompactPlus2928.checked2929,CompactPlus2928.small2929,CompactPlus2928.nodes2929,NodePlus45.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus2928.p2930,GridPlus.atNode 2930,GridPlus.atNode 2931,NodePlus45.w50,CompactPlus2928.checked2930,CompactPlus2928.small2930,CompactPlus2928.nodes2930,NodePlus45.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus2928.p2931,GridPlus.atNode 2931,GridPlus.atNode 2932,NodePlus45.w51,CompactPlus2928.checked2931,CompactPlus2928.small2931,CompactPlus2928.nodes2931,NodePlus45.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus2928.p2932,GridPlus.atNode 2932,GridPlus.atNode 2933,NodePlus45.w52,CompactPlus2928.checked2932,CompactPlus2928.small2932,CompactPlus2928.nodes2932,NodePlus45.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus2928.p2933,GridPlus.atNode 2933,GridPlus.atNode 2934,NodePlus45.w53,CompactPlus2928.checked2933,CompactPlus2928.small2933,CompactPlus2928.nodes2933,NodePlus45.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus2928.p2934,GridPlus.atNode 2934,GridPlus.atNode 2935,NodePlus45.w54,CompactPlus2928.checked2934,CompactPlus2928.small2934,CompactPlus2928.nodes2934,NodePlus45.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus2928.p2935,GridPlus.atNode 2935,GridPlus.atNode 2936,NodePlus45.w55,CompactPlus2928.checked2935,CompactPlus2928.small2935,CompactPlus2928.nodes2935,NodePlus45.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus2928.p2936,GridPlus.atNode 2936,GridPlus.atNode 2937,NodePlus45.w56,CompactPlus2928.checked2936,CompactPlus2928.small2936,CompactPlus2928.nodes2936,NodePlus45.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus2928.p2937,GridPlus.atNode 2937,GridPlus.atNode 2938,NodePlus45.w57,CompactPlus2928.checked2937,CompactPlus2928.small2937,CompactPlus2928.nodes2937,NodePlus45.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus2928.p2938,GridPlus.atNode 2938,GridPlus.atNode 2939,NodePlus45.w58,CompactPlus2928.checked2938,CompactPlus2928.small2938,CompactPlus2928.nodes2938,NodePlus45.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus2928.p2939,GridPlus.atNode 2939,GridPlus.atNode 2940,NodePlus45.w59,CompactPlus2928.checked2939,CompactPlus2928.small2939,CompactPlus2928.nodes2939,NodePlus45.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus2928.p2940,GridPlus.atNode 2940,GridPlus.atNode 2941,NodePlus45.w60,CompactPlus2928.checked2940,CompactPlus2928.small2940,CompactPlus2928.nodes2940,NodePlus45.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus2928.p2941,GridPlus.atNode 2941,GridPlus.atNode 2942,NodePlus45.w61,CompactPlus2928.checked2941,CompactPlus2928.small2941,CompactPlus2928.nodes2941,NodePlus45.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus2928.p2942,GridPlus.atNode 2942,GridPlus.atNode 2943,NodePlus45.w62,CompactPlus2928.checked2942,CompactPlus2928.small2942,CompactPlus2928.nodes2942,NodePlus45.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus2928.p2943,GridPlus.atNode 2943,GridPlus.atNode 2944,NodePlus45.w63,CompactPlus2928.checked2943,CompactPlus2928.small2943,CompactPlus2928.nodes2943,NodePlus45.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (2880+j) ∧
    (atRow j).right=GridPlus.atNode (2880+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus45
