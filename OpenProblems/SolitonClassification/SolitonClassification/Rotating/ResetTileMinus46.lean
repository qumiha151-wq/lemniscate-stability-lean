import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus2944
import SolitonClassification.Rotating.ResetPackedMinus2960
import SolitonClassification.Rotating.ResetPackedMinus2976
import SolitonClassification.Rotating.ResetPackedMinus2992
namespace SolitonClassification.Rotating.DyadicReset.TileMinus46
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2944.p2944,GridMinus.atNode 2944,GridMinus.atNode 2945,NodeMinus46.w0,CompactMinus2944.checked2944,CompactMinus2944.small2944,CompactMinus2944.nodes2944,NodeMinus46.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2944.p2945,GridMinus.atNode 2945,GridMinus.atNode 2946,NodeMinus46.w1,CompactMinus2944.checked2945,CompactMinus2944.small2945,CompactMinus2944.nodes2945,NodeMinus46.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2944.p2946,GridMinus.atNode 2946,GridMinus.atNode 2947,NodeMinus46.w2,CompactMinus2944.checked2946,CompactMinus2944.small2946,CompactMinus2944.nodes2946,NodeMinus46.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2944.p2947,GridMinus.atNode 2947,GridMinus.atNode 2948,NodeMinus46.w3,CompactMinus2944.checked2947,CompactMinus2944.small2947,CompactMinus2944.nodes2947,NodeMinus46.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2944.p2948,GridMinus.atNode 2948,GridMinus.atNode 2949,NodeMinus46.w4,CompactMinus2944.checked2948,CompactMinus2944.small2948,CompactMinus2944.nodes2948,NodeMinus46.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2944.p2949,GridMinus.atNode 2949,GridMinus.atNode 2950,NodeMinus46.w5,CompactMinus2944.checked2949,CompactMinus2944.small2949,CompactMinus2944.nodes2949,NodeMinus46.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2944.p2950,GridMinus.atNode 2950,GridMinus.atNode 2951,NodeMinus46.w6,CompactMinus2944.checked2950,CompactMinus2944.small2950,CompactMinus2944.nodes2950,NodeMinus46.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2944.p2951,GridMinus.atNode 2951,GridMinus.atNode 2952,NodeMinus46.w7,CompactMinus2944.checked2951,CompactMinus2944.small2951,CompactMinus2944.nodes2951,NodeMinus46.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2944.p2952,GridMinus.atNode 2952,GridMinus.atNode 2953,NodeMinus46.w8,CompactMinus2944.checked2952,CompactMinus2944.small2952,CompactMinus2944.nodes2952,NodeMinus46.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2944.p2953,GridMinus.atNode 2953,GridMinus.atNode 2954,NodeMinus46.w9,CompactMinus2944.checked2953,CompactMinus2944.small2953,CompactMinus2944.nodes2953,NodeMinus46.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2944.p2954,GridMinus.atNode 2954,GridMinus.atNode 2955,NodeMinus46.w10,CompactMinus2944.checked2954,CompactMinus2944.small2954,CompactMinus2944.nodes2954,NodeMinus46.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2944.p2955,GridMinus.atNode 2955,GridMinus.atNode 2956,NodeMinus46.w11,CompactMinus2944.checked2955,CompactMinus2944.small2955,CompactMinus2944.nodes2955,NodeMinus46.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2944.p2956,GridMinus.atNode 2956,GridMinus.atNode 2957,NodeMinus46.w12,CompactMinus2944.checked2956,CompactMinus2944.small2956,CompactMinus2944.nodes2956,NodeMinus46.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2944.p2957,GridMinus.atNode 2957,GridMinus.atNode 2958,NodeMinus46.w13,CompactMinus2944.checked2957,CompactMinus2944.small2957,CompactMinus2944.nodes2957,NodeMinus46.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2944.p2958,GridMinus.atNode 2958,GridMinus.atNode 2959,NodeMinus46.w14,CompactMinus2944.checked2958,CompactMinus2944.small2958,CompactMinus2944.nodes2958,NodeMinus46.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2944.p2959,GridMinus.atNode 2959,GridMinus.atNode 2960,NodeMinus46.w15,CompactMinus2944.checked2959,CompactMinus2944.small2959,CompactMinus2944.nodes2959,NodeMinus46.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2960.p2960,GridMinus.atNode 2960,GridMinus.atNode 2961,NodeMinus46.w16,CompactMinus2960.checked2960,CompactMinus2960.small2960,CompactMinus2960.nodes2960,NodeMinus46.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2960.p2961,GridMinus.atNode 2961,GridMinus.atNode 2962,NodeMinus46.w17,CompactMinus2960.checked2961,CompactMinus2960.small2961,CompactMinus2960.nodes2961,NodeMinus46.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2960.p2962,GridMinus.atNode 2962,GridMinus.atNode 2963,NodeMinus46.w18,CompactMinus2960.checked2962,CompactMinus2960.small2962,CompactMinus2960.nodes2962,NodeMinus46.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2960.p2963,GridMinus.atNode 2963,GridMinus.atNode 2964,NodeMinus46.w19,CompactMinus2960.checked2963,CompactMinus2960.small2963,CompactMinus2960.nodes2963,NodeMinus46.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2960.p2964,GridMinus.atNode 2964,GridMinus.atNode 2965,NodeMinus46.w20,CompactMinus2960.checked2964,CompactMinus2960.small2964,CompactMinus2960.nodes2964,NodeMinus46.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2960.p2965,GridMinus.atNode 2965,GridMinus.atNode 2966,NodeMinus46.w21,CompactMinus2960.checked2965,CompactMinus2960.small2965,CompactMinus2960.nodes2965,NodeMinus46.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2960.p2966,GridMinus.atNode 2966,GridMinus.atNode 2967,NodeMinus46.w22,CompactMinus2960.checked2966,CompactMinus2960.small2966,CompactMinus2960.nodes2966,NodeMinus46.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2960.p2967,GridMinus.atNode 2967,GridMinus.atNode 2968,NodeMinus46.w23,CompactMinus2960.checked2967,CompactMinus2960.small2967,CompactMinus2960.nodes2967,NodeMinus46.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2960.p2968,GridMinus.atNode 2968,GridMinus.atNode 2969,NodeMinus46.w24,CompactMinus2960.checked2968,CompactMinus2960.small2968,CompactMinus2960.nodes2968,NodeMinus46.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2960.p2969,GridMinus.atNode 2969,GridMinus.atNode 2970,NodeMinus46.w25,CompactMinus2960.checked2969,CompactMinus2960.small2969,CompactMinus2960.nodes2969,NodeMinus46.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2960.p2970,GridMinus.atNode 2970,GridMinus.atNode 2971,NodeMinus46.w26,CompactMinus2960.checked2970,CompactMinus2960.small2970,CompactMinus2960.nodes2970,NodeMinus46.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2960.p2971,GridMinus.atNode 2971,GridMinus.atNode 2972,NodeMinus46.w27,CompactMinus2960.checked2971,CompactMinus2960.small2971,CompactMinus2960.nodes2971,NodeMinus46.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2960.p2972,GridMinus.atNode 2972,GridMinus.atNode 2973,NodeMinus46.w28,CompactMinus2960.checked2972,CompactMinus2960.small2972,CompactMinus2960.nodes2972,NodeMinus46.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2960.p2973,GridMinus.atNode 2973,GridMinus.atNode 2974,NodeMinus46.w29,CompactMinus2960.checked2973,CompactMinus2960.small2973,CompactMinus2960.nodes2973,NodeMinus46.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2960.p2974,GridMinus.atNode 2974,GridMinus.atNode 2975,NodeMinus46.w30,CompactMinus2960.checked2974,CompactMinus2960.small2974,CompactMinus2960.nodes2974,NodeMinus46.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2960.p2975,GridMinus.atNode 2975,GridMinus.atNode 2976,NodeMinus46.w31,CompactMinus2960.checked2975,CompactMinus2960.small2975,CompactMinus2960.nodes2975,NodeMinus46.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2976.p2976,GridMinus.atNode 2976,GridMinus.atNode 2977,NodeMinus46.w32,CompactMinus2976.checked2976,CompactMinus2976.small2976,CompactMinus2976.nodes2976,NodeMinus46.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2976.p2977,GridMinus.atNode 2977,GridMinus.atNode 2978,NodeMinus46.w33,CompactMinus2976.checked2977,CompactMinus2976.small2977,CompactMinus2976.nodes2977,NodeMinus46.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2976.p2978,GridMinus.atNode 2978,GridMinus.atNode 2979,NodeMinus46.w34,CompactMinus2976.checked2978,CompactMinus2976.small2978,CompactMinus2976.nodes2978,NodeMinus46.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2976.p2979,GridMinus.atNode 2979,GridMinus.atNode 2980,NodeMinus46.w35,CompactMinus2976.checked2979,CompactMinus2976.small2979,CompactMinus2976.nodes2979,NodeMinus46.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2976.p2980,GridMinus.atNode 2980,GridMinus.atNode 2981,NodeMinus46.w36,CompactMinus2976.checked2980,CompactMinus2976.small2980,CompactMinus2976.nodes2980,NodeMinus46.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2976.p2981,GridMinus.atNode 2981,GridMinus.atNode 2982,NodeMinus46.w37,CompactMinus2976.checked2981,CompactMinus2976.small2981,CompactMinus2976.nodes2981,NodeMinus46.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2976.p2982,GridMinus.atNode 2982,GridMinus.atNode 2983,NodeMinus46.w38,CompactMinus2976.checked2982,CompactMinus2976.small2982,CompactMinus2976.nodes2982,NodeMinus46.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2976.p2983,GridMinus.atNode 2983,GridMinus.atNode 2984,NodeMinus46.w39,CompactMinus2976.checked2983,CompactMinus2976.small2983,CompactMinus2976.nodes2983,NodeMinus46.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2976.p2984,GridMinus.atNode 2984,GridMinus.atNode 2985,NodeMinus46.w40,CompactMinus2976.checked2984,CompactMinus2976.small2984,CompactMinus2976.nodes2984,NodeMinus46.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2976.p2985,GridMinus.atNode 2985,GridMinus.atNode 2986,NodeMinus46.w41,CompactMinus2976.checked2985,CompactMinus2976.small2985,CompactMinus2976.nodes2985,NodeMinus46.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2976.p2986,GridMinus.atNode 2986,GridMinus.atNode 2987,NodeMinus46.w42,CompactMinus2976.checked2986,CompactMinus2976.small2986,CompactMinus2976.nodes2986,NodeMinus46.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2976.p2987,GridMinus.atNode 2987,GridMinus.atNode 2988,NodeMinus46.w43,CompactMinus2976.checked2987,CompactMinus2976.small2987,CompactMinus2976.nodes2987,NodeMinus46.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2976.p2988,GridMinus.atNode 2988,GridMinus.atNode 2989,NodeMinus46.w44,CompactMinus2976.checked2988,CompactMinus2976.small2988,CompactMinus2976.nodes2988,NodeMinus46.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2976.p2989,GridMinus.atNode 2989,GridMinus.atNode 2990,NodeMinus46.w45,CompactMinus2976.checked2989,CompactMinus2976.small2989,CompactMinus2976.nodes2989,NodeMinus46.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2976.p2990,GridMinus.atNode 2990,GridMinus.atNode 2991,NodeMinus46.w46,CompactMinus2976.checked2990,CompactMinus2976.small2990,CompactMinus2976.nodes2990,NodeMinus46.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2976.p2991,GridMinus.atNode 2991,GridMinus.atNode 2992,NodeMinus46.w47,CompactMinus2976.checked2991,CompactMinus2976.small2991,CompactMinus2976.nodes2991,NodeMinus46.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2992.p2992,GridMinus.atNode 2992,GridMinus.atNode 2993,NodeMinus46.w48,CompactMinus2992.checked2992,CompactMinus2992.small2992,CompactMinus2992.nodes2992,NodeMinus46.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2992.p2993,GridMinus.atNode 2993,GridMinus.atNode 2994,NodeMinus46.w49,CompactMinus2992.checked2993,CompactMinus2992.small2993,CompactMinus2992.nodes2993,NodeMinus46.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2992.p2994,GridMinus.atNode 2994,GridMinus.atNode 2995,NodeMinus46.w50,CompactMinus2992.checked2994,CompactMinus2992.small2994,CompactMinus2992.nodes2994,NodeMinus46.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2992.p2995,GridMinus.atNode 2995,GridMinus.atNode 2996,NodeMinus46.w51,CompactMinus2992.checked2995,CompactMinus2992.small2995,CompactMinus2992.nodes2995,NodeMinus46.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2992.p2996,GridMinus.atNode 2996,GridMinus.atNode 2997,NodeMinus46.w52,CompactMinus2992.checked2996,CompactMinus2992.small2996,CompactMinus2992.nodes2996,NodeMinus46.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2992.p2997,GridMinus.atNode 2997,GridMinus.atNode 2998,NodeMinus46.w53,CompactMinus2992.checked2997,CompactMinus2992.small2997,CompactMinus2992.nodes2997,NodeMinus46.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2992.p2998,GridMinus.atNode 2998,GridMinus.atNode 2999,NodeMinus46.w54,CompactMinus2992.checked2998,CompactMinus2992.small2998,CompactMinus2992.nodes2998,NodeMinus46.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2992.p2999,GridMinus.atNode 2999,GridMinus.atNode 3000,NodeMinus46.w55,CompactMinus2992.checked2999,CompactMinus2992.small2999,CompactMinus2992.nodes2999,NodeMinus46.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2992.p3000,GridMinus.atNode 3000,GridMinus.atNode 3001,NodeMinus46.w56,CompactMinus2992.checked3000,CompactMinus2992.small3000,CompactMinus2992.nodes3000,NodeMinus46.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2992.p3001,GridMinus.atNode 3001,GridMinus.atNode 3002,NodeMinus46.w57,CompactMinus2992.checked3001,CompactMinus2992.small3001,CompactMinus2992.nodes3001,NodeMinus46.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2992.p3002,GridMinus.atNode 3002,GridMinus.atNode 3003,NodeMinus46.w58,CompactMinus2992.checked3002,CompactMinus2992.small3002,CompactMinus2992.nodes3002,NodeMinus46.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2992.p3003,GridMinus.atNode 3003,GridMinus.atNode 3004,NodeMinus46.w59,CompactMinus2992.checked3003,CompactMinus2992.small3003,CompactMinus2992.nodes3003,NodeMinus46.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2992.p3004,GridMinus.atNode 3004,GridMinus.atNode 3005,NodeMinus46.w60,CompactMinus2992.checked3004,CompactMinus2992.small3004,CompactMinus2992.nodes3004,NodeMinus46.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2992.p3005,GridMinus.atNode 3005,GridMinus.atNode 3006,NodeMinus46.w61,CompactMinus2992.checked3005,CompactMinus2992.small3005,CompactMinus2992.nodes3005,NodeMinus46.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2992.p3006,GridMinus.atNode 3006,GridMinus.atNode 3007,NodeMinus46.w62,CompactMinus2992.checked3006,CompactMinus2992.small3006,CompactMinus2992.nodes3006,NodeMinus46.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus2992.p3007,GridMinus.atNode 3007,GridMinus.atNode 3008,NodeMinus46.w63,CompactMinus2992.checked3007,CompactMinus2992.small3007,CompactMinus2992.nodes3007,NodeMinus46.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (2944+j) ∧
    (atRow j).right=GridMinus.atNode (2944+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus46
