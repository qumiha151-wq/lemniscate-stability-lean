import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus2880
import SolitonClassification.Rotating.ResetPackedMinus2896
import SolitonClassification.Rotating.ResetPackedMinus2912
import SolitonClassification.Rotating.ResetPackedMinus2928
namespace SolitonClassification.Rotating.DyadicReset.TileMinus45
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2880.p2880,GridMinus.atNode 2880,GridMinus.atNode 2881,NodeMinus45.w0,CompactMinus2880.checked2880,CompactMinus2880.small2880,CompactMinus2880.nodes2880,NodeMinus45.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2880.p2881,GridMinus.atNode 2881,GridMinus.atNode 2882,NodeMinus45.w1,CompactMinus2880.checked2881,CompactMinus2880.small2881,CompactMinus2880.nodes2881,NodeMinus45.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2880.p2882,GridMinus.atNode 2882,GridMinus.atNode 2883,NodeMinus45.w2,CompactMinus2880.checked2882,CompactMinus2880.small2882,CompactMinus2880.nodes2882,NodeMinus45.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2880.p2883,GridMinus.atNode 2883,GridMinus.atNode 2884,NodeMinus45.w3,CompactMinus2880.checked2883,CompactMinus2880.small2883,CompactMinus2880.nodes2883,NodeMinus45.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2880.p2884,GridMinus.atNode 2884,GridMinus.atNode 2885,NodeMinus45.w4,CompactMinus2880.checked2884,CompactMinus2880.small2884,CompactMinus2880.nodes2884,NodeMinus45.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2880.p2885,GridMinus.atNode 2885,GridMinus.atNode 2886,NodeMinus45.w5,CompactMinus2880.checked2885,CompactMinus2880.small2885,CompactMinus2880.nodes2885,NodeMinus45.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2880.p2886,GridMinus.atNode 2886,GridMinus.atNode 2887,NodeMinus45.w6,CompactMinus2880.checked2886,CompactMinus2880.small2886,CompactMinus2880.nodes2886,NodeMinus45.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2880.p2887,GridMinus.atNode 2887,GridMinus.atNode 2888,NodeMinus45.w7,CompactMinus2880.checked2887,CompactMinus2880.small2887,CompactMinus2880.nodes2887,NodeMinus45.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2880.p2888,GridMinus.atNode 2888,GridMinus.atNode 2889,NodeMinus45.w8,CompactMinus2880.checked2888,CompactMinus2880.small2888,CompactMinus2880.nodes2888,NodeMinus45.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2880.p2889,GridMinus.atNode 2889,GridMinus.atNode 2890,NodeMinus45.w9,CompactMinus2880.checked2889,CompactMinus2880.small2889,CompactMinus2880.nodes2889,NodeMinus45.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2880.p2890,GridMinus.atNode 2890,GridMinus.atNode 2891,NodeMinus45.w10,CompactMinus2880.checked2890,CompactMinus2880.small2890,CompactMinus2880.nodes2890,NodeMinus45.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2880.p2891,GridMinus.atNode 2891,GridMinus.atNode 2892,NodeMinus45.w11,CompactMinus2880.checked2891,CompactMinus2880.small2891,CompactMinus2880.nodes2891,NodeMinus45.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2880.p2892,GridMinus.atNode 2892,GridMinus.atNode 2893,NodeMinus45.w12,CompactMinus2880.checked2892,CompactMinus2880.small2892,CompactMinus2880.nodes2892,NodeMinus45.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2880.p2893,GridMinus.atNode 2893,GridMinus.atNode 2894,NodeMinus45.w13,CompactMinus2880.checked2893,CompactMinus2880.small2893,CompactMinus2880.nodes2893,NodeMinus45.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2880.p2894,GridMinus.atNode 2894,GridMinus.atNode 2895,NodeMinus45.w14,CompactMinus2880.checked2894,CompactMinus2880.small2894,CompactMinus2880.nodes2894,NodeMinus45.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2880.p2895,GridMinus.atNode 2895,GridMinus.atNode 2896,NodeMinus45.w15,CompactMinus2880.checked2895,CompactMinus2880.small2895,CompactMinus2880.nodes2895,NodeMinus45.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2896.p2896,GridMinus.atNode 2896,GridMinus.atNode 2897,NodeMinus45.w16,CompactMinus2896.checked2896,CompactMinus2896.small2896,CompactMinus2896.nodes2896,NodeMinus45.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2896.p2897,GridMinus.atNode 2897,GridMinus.atNode 2898,NodeMinus45.w17,CompactMinus2896.checked2897,CompactMinus2896.small2897,CompactMinus2896.nodes2897,NodeMinus45.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2896.p2898,GridMinus.atNode 2898,GridMinus.atNode 2899,NodeMinus45.w18,CompactMinus2896.checked2898,CompactMinus2896.small2898,CompactMinus2896.nodes2898,NodeMinus45.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2896.p2899,GridMinus.atNode 2899,GridMinus.atNode 2900,NodeMinus45.w19,CompactMinus2896.checked2899,CompactMinus2896.small2899,CompactMinus2896.nodes2899,NodeMinus45.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2896.p2900,GridMinus.atNode 2900,GridMinus.atNode 2901,NodeMinus45.w20,CompactMinus2896.checked2900,CompactMinus2896.small2900,CompactMinus2896.nodes2900,NodeMinus45.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2896.p2901,GridMinus.atNode 2901,GridMinus.atNode 2902,NodeMinus45.w21,CompactMinus2896.checked2901,CompactMinus2896.small2901,CompactMinus2896.nodes2901,NodeMinus45.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2896.p2902,GridMinus.atNode 2902,GridMinus.atNode 2903,NodeMinus45.w22,CompactMinus2896.checked2902,CompactMinus2896.small2902,CompactMinus2896.nodes2902,NodeMinus45.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2896.p2903,GridMinus.atNode 2903,GridMinus.atNode 2904,NodeMinus45.w23,CompactMinus2896.checked2903,CompactMinus2896.small2903,CompactMinus2896.nodes2903,NodeMinus45.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2896.p2904,GridMinus.atNode 2904,GridMinus.atNode 2905,NodeMinus45.w24,CompactMinus2896.checked2904,CompactMinus2896.small2904,CompactMinus2896.nodes2904,NodeMinus45.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2896.p2905,GridMinus.atNode 2905,GridMinus.atNode 2906,NodeMinus45.w25,CompactMinus2896.checked2905,CompactMinus2896.small2905,CompactMinus2896.nodes2905,NodeMinus45.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2896.p2906,GridMinus.atNode 2906,GridMinus.atNode 2907,NodeMinus45.w26,CompactMinus2896.checked2906,CompactMinus2896.small2906,CompactMinus2896.nodes2906,NodeMinus45.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2896.p2907,GridMinus.atNode 2907,GridMinus.atNode 2908,NodeMinus45.w27,CompactMinus2896.checked2907,CompactMinus2896.small2907,CompactMinus2896.nodes2907,NodeMinus45.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2896.p2908,GridMinus.atNode 2908,GridMinus.atNode 2909,NodeMinus45.w28,CompactMinus2896.checked2908,CompactMinus2896.small2908,CompactMinus2896.nodes2908,NodeMinus45.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2896.p2909,GridMinus.atNode 2909,GridMinus.atNode 2910,NodeMinus45.w29,CompactMinus2896.checked2909,CompactMinus2896.small2909,CompactMinus2896.nodes2909,NodeMinus45.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2896.p2910,GridMinus.atNode 2910,GridMinus.atNode 2911,NodeMinus45.w30,CompactMinus2896.checked2910,CompactMinus2896.small2910,CompactMinus2896.nodes2910,NodeMinus45.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2896.p2911,GridMinus.atNode 2911,GridMinus.atNode 2912,NodeMinus45.w31,CompactMinus2896.checked2911,CompactMinus2896.small2911,CompactMinus2896.nodes2911,NodeMinus45.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2912.p2912,GridMinus.atNode 2912,GridMinus.atNode 2913,NodeMinus45.w32,CompactMinus2912.checked2912,CompactMinus2912.small2912,CompactMinus2912.nodes2912,NodeMinus45.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2912.p2913,GridMinus.atNode 2913,GridMinus.atNode 2914,NodeMinus45.w33,CompactMinus2912.checked2913,CompactMinus2912.small2913,CompactMinus2912.nodes2913,NodeMinus45.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2912.p2914,GridMinus.atNode 2914,GridMinus.atNode 2915,NodeMinus45.w34,CompactMinus2912.checked2914,CompactMinus2912.small2914,CompactMinus2912.nodes2914,NodeMinus45.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2912.p2915,GridMinus.atNode 2915,GridMinus.atNode 2916,NodeMinus45.w35,CompactMinus2912.checked2915,CompactMinus2912.small2915,CompactMinus2912.nodes2915,NodeMinus45.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2912.p2916,GridMinus.atNode 2916,GridMinus.atNode 2917,NodeMinus45.w36,CompactMinus2912.checked2916,CompactMinus2912.small2916,CompactMinus2912.nodes2916,NodeMinus45.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2912.p2917,GridMinus.atNode 2917,GridMinus.atNode 2918,NodeMinus45.w37,CompactMinus2912.checked2917,CompactMinus2912.small2917,CompactMinus2912.nodes2917,NodeMinus45.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2912.p2918,GridMinus.atNode 2918,GridMinus.atNode 2919,NodeMinus45.w38,CompactMinus2912.checked2918,CompactMinus2912.small2918,CompactMinus2912.nodes2918,NodeMinus45.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2912.p2919,GridMinus.atNode 2919,GridMinus.atNode 2920,NodeMinus45.w39,CompactMinus2912.checked2919,CompactMinus2912.small2919,CompactMinus2912.nodes2919,NodeMinus45.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2912.p2920,GridMinus.atNode 2920,GridMinus.atNode 2921,NodeMinus45.w40,CompactMinus2912.checked2920,CompactMinus2912.small2920,CompactMinus2912.nodes2920,NodeMinus45.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2912.p2921,GridMinus.atNode 2921,GridMinus.atNode 2922,NodeMinus45.w41,CompactMinus2912.checked2921,CompactMinus2912.small2921,CompactMinus2912.nodes2921,NodeMinus45.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2912.p2922,GridMinus.atNode 2922,GridMinus.atNode 2923,NodeMinus45.w42,CompactMinus2912.checked2922,CompactMinus2912.small2922,CompactMinus2912.nodes2922,NodeMinus45.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2912.p2923,GridMinus.atNode 2923,GridMinus.atNode 2924,NodeMinus45.w43,CompactMinus2912.checked2923,CompactMinus2912.small2923,CompactMinus2912.nodes2923,NodeMinus45.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2912.p2924,GridMinus.atNode 2924,GridMinus.atNode 2925,NodeMinus45.w44,CompactMinus2912.checked2924,CompactMinus2912.small2924,CompactMinus2912.nodes2924,NodeMinus45.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2912.p2925,GridMinus.atNode 2925,GridMinus.atNode 2926,NodeMinus45.w45,CompactMinus2912.checked2925,CompactMinus2912.small2925,CompactMinus2912.nodes2925,NodeMinus45.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2912.p2926,GridMinus.atNode 2926,GridMinus.atNode 2927,NodeMinus45.w46,CompactMinus2912.checked2926,CompactMinus2912.small2926,CompactMinus2912.nodes2926,NodeMinus45.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2912.p2927,GridMinus.atNode 2927,GridMinus.atNode 2928,NodeMinus45.w47,CompactMinus2912.checked2927,CompactMinus2912.small2927,CompactMinus2912.nodes2927,NodeMinus45.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2928.p2928,GridMinus.atNode 2928,GridMinus.atNode 2929,NodeMinus45.w48,CompactMinus2928.checked2928,CompactMinus2928.small2928,CompactMinus2928.nodes2928,NodeMinus45.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2928.p2929,GridMinus.atNode 2929,GridMinus.atNode 2930,NodeMinus45.w49,CompactMinus2928.checked2929,CompactMinus2928.small2929,CompactMinus2928.nodes2929,NodeMinus45.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2928.p2930,GridMinus.atNode 2930,GridMinus.atNode 2931,NodeMinus45.w50,CompactMinus2928.checked2930,CompactMinus2928.small2930,CompactMinus2928.nodes2930,NodeMinus45.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2928.p2931,GridMinus.atNode 2931,GridMinus.atNode 2932,NodeMinus45.w51,CompactMinus2928.checked2931,CompactMinus2928.small2931,CompactMinus2928.nodes2931,NodeMinus45.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2928.p2932,GridMinus.atNode 2932,GridMinus.atNode 2933,NodeMinus45.w52,CompactMinus2928.checked2932,CompactMinus2928.small2932,CompactMinus2928.nodes2932,NodeMinus45.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2928.p2933,GridMinus.atNode 2933,GridMinus.atNode 2934,NodeMinus45.w53,CompactMinus2928.checked2933,CompactMinus2928.small2933,CompactMinus2928.nodes2933,NodeMinus45.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2928.p2934,GridMinus.atNode 2934,GridMinus.atNode 2935,NodeMinus45.w54,CompactMinus2928.checked2934,CompactMinus2928.small2934,CompactMinus2928.nodes2934,NodeMinus45.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2928.p2935,GridMinus.atNode 2935,GridMinus.atNode 2936,NodeMinus45.w55,CompactMinus2928.checked2935,CompactMinus2928.small2935,CompactMinus2928.nodes2935,NodeMinus45.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2928.p2936,GridMinus.atNode 2936,GridMinus.atNode 2937,NodeMinus45.w56,CompactMinus2928.checked2936,CompactMinus2928.small2936,CompactMinus2928.nodes2936,NodeMinus45.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2928.p2937,GridMinus.atNode 2937,GridMinus.atNode 2938,NodeMinus45.w57,CompactMinus2928.checked2937,CompactMinus2928.small2937,CompactMinus2928.nodes2937,NodeMinus45.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2928.p2938,GridMinus.atNode 2938,GridMinus.atNode 2939,NodeMinus45.w58,CompactMinus2928.checked2938,CompactMinus2928.small2938,CompactMinus2928.nodes2938,NodeMinus45.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2928.p2939,GridMinus.atNode 2939,GridMinus.atNode 2940,NodeMinus45.w59,CompactMinus2928.checked2939,CompactMinus2928.small2939,CompactMinus2928.nodes2939,NodeMinus45.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2928.p2940,GridMinus.atNode 2940,GridMinus.atNode 2941,NodeMinus45.w60,CompactMinus2928.checked2940,CompactMinus2928.small2940,CompactMinus2928.nodes2940,NodeMinus45.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2928.p2941,GridMinus.atNode 2941,GridMinus.atNode 2942,NodeMinus45.w61,CompactMinus2928.checked2941,CompactMinus2928.small2941,CompactMinus2928.nodes2941,NodeMinus45.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2928.p2942,GridMinus.atNode 2942,GridMinus.atNode 2943,NodeMinus45.w62,CompactMinus2928.checked2942,CompactMinus2928.small2942,CompactMinus2928.nodes2942,NodeMinus45.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2928.p2943,GridMinus.atNode 2943,GridMinus.atNode 2944,NodeMinus45.w63,CompactMinus2928.checked2943,CompactMinus2928.small2943,CompactMinus2928.nodes2943,NodeMinus45.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (2880+j) ∧
    (atRow j).right=GridMinus.atNode (2880+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus45
