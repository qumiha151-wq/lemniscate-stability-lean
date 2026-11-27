import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus2944
import SolitonClassification.Rotating.ResetPackedPlus2960
import SolitonClassification.Rotating.ResetPackedPlus2976
import SolitonClassification.Rotating.ResetPackedPlus2992
namespace SolitonClassification.Rotating.DyadicReset.TilePlus46
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus2944.p2944,GridPlus.atNode 2944,GridPlus.atNode 2945,NodePlus46.w0,CompactPlus2944.checked2944,CompactPlus2944.small2944,CompactPlus2944.nodes2944,NodePlus46.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus2944.p2945,GridPlus.atNode 2945,GridPlus.atNode 2946,NodePlus46.w1,CompactPlus2944.checked2945,CompactPlus2944.small2945,CompactPlus2944.nodes2945,NodePlus46.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus2944.p2946,GridPlus.atNode 2946,GridPlus.atNode 2947,NodePlus46.w2,CompactPlus2944.checked2946,CompactPlus2944.small2946,CompactPlus2944.nodes2946,NodePlus46.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus2944.p2947,GridPlus.atNode 2947,GridPlus.atNode 2948,NodePlus46.w3,CompactPlus2944.checked2947,CompactPlus2944.small2947,CompactPlus2944.nodes2947,NodePlus46.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus2944.p2948,GridPlus.atNode 2948,GridPlus.atNode 2949,NodePlus46.w4,CompactPlus2944.checked2948,CompactPlus2944.small2948,CompactPlus2944.nodes2948,NodePlus46.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus2944.p2949,GridPlus.atNode 2949,GridPlus.atNode 2950,NodePlus46.w5,CompactPlus2944.checked2949,CompactPlus2944.small2949,CompactPlus2944.nodes2949,NodePlus46.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus2944.p2950,GridPlus.atNode 2950,GridPlus.atNode 2951,NodePlus46.w6,CompactPlus2944.checked2950,CompactPlus2944.small2950,CompactPlus2944.nodes2950,NodePlus46.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus2944.p2951,GridPlus.atNode 2951,GridPlus.atNode 2952,NodePlus46.w7,CompactPlus2944.checked2951,CompactPlus2944.small2951,CompactPlus2944.nodes2951,NodePlus46.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus2944.p2952,GridPlus.atNode 2952,GridPlus.atNode 2953,NodePlus46.w8,CompactPlus2944.checked2952,CompactPlus2944.small2952,CompactPlus2944.nodes2952,NodePlus46.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus2944.p2953,GridPlus.atNode 2953,GridPlus.atNode 2954,NodePlus46.w9,CompactPlus2944.checked2953,CompactPlus2944.small2953,CompactPlus2944.nodes2953,NodePlus46.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus2944.p2954,GridPlus.atNode 2954,GridPlus.atNode 2955,NodePlus46.w10,CompactPlus2944.checked2954,CompactPlus2944.small2954,CompactPlus2944.nodes2954,NodePlus46.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus2944.p2955,GridPlus.atNode 2955,GridPlus.atNode 2956,NodePlus46.w11,CompactPlus2944.checked2955,CompactPlus2944.small2955,CompactPlus2944.nodes2955,NodePlus46.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus2944.p2956,GridPlus.atNode 2956,GridPlus.atNode 2957,NodePlus46.w12,CompactPlus2944.checked2956,CompactPlus2944.small2956,CompactPlus2944.nodes2956,NodePlus46.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus2944.p2957,GridPlus.atNode 2957,GridPlus.atNode 2958,NodePlus46.w13,CompactPlus2944.checked2957,CompactPlus2944.small2957,CompactPlus2944.nodes2957,NodePlus46.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus2944.p2958,GridPlus.atNode 2958,GridPlus.atNode 2959,NodePlus46.w14,CompactPlus2944.checked2958,CompactPlus2944.small2958,CompactPlus2944.nodes2958,NodePlus46.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus2944.p2959,GridPlus.atNode 2959,GridPlus.atNode 2960,NodePlus46.w15,CompactPlus2944.checked2959,CompactPlus2944.small2959,CompactPlus2944.nodes2959,NodePlus46.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus2960.p2960,GridPlus.atNode 2960,GridPlus.atNode 2961,NodePlus46.w16,CompactPlus2960.checked2960,CompactPlus2960.small2960,CompactPlus2960.nodes2960,NodePlus46.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus2960.p2961,GridPlus.atNode 2961,GridPlus.atNode 2962,NodePlus46.w17,CompactPlus2960.checked2961,CompactPlus2960.small2961,CompactPlus2960.nodes2961,NodePlus46.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus2960.p2962,GridPlus.atNode 2962,GridPlus.atNode 2963,NodePlus46.w18,CompactPlus2960.checked2962,CompactPlus2960.small2962,CompactPlus2960.nodes2962,NodePlus46.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus2960.p2963,GridPlus.atNode 2963,GridPlus.atNode 2964,NodePlus46.w19,CompactPlus2960.checked2963,CompactPlus2960.small2963,CompactPlus2960.nodes2963,NodePlus46.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus2960.p2964,GridPlus.atNode 2964,GridPlus.atNode 2965,NodePlus46.w20,CompactPlus2960.checked2964,CompactPlus2960.small2964,CompactPlus2960.nodes2964,NodePlus46.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus2960.p2965,GridPlus.atNode 2965,GridPlus.atNode 2966,NodePlus46.w21,CompactPlus2960.checked2965,CompactPlus2960.small2965,CompactPlus2960.nodes2965,NodePlus46.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus2960.p2966,GridPlus.atNode 2966,GridPlus.atNode 2967,NodePlus46.w22,CompactPlus2960.checked2966,CompactPlus2960.small2966,CompactPlus2960.nodes2966,NodePlus46.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus2960.p2967,GridPlus.atNode 2967,GridPlus.atNode 2968,NodePlus46.w23,CompactPlus2960.checked2967,CompactPlus2960.small2967,CompactPlus2960.nodes2967,NodePlus46.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus2960.p2968,GridPlus.atNode 2968,GridPlus.atNode 2969,NodePlus46.w24,CompactPlus2960.checked2968,CompactPlus2960.small2968,CompactPlus2960.nodes2968,NodePlus46.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus2960.p2969,GridPlus.atNode 2969,GridPlus.atNode 2970,NodePlus46.w25,CompactPlus2960.checked2969,CompactPlus2960.small2969,CompactPlus2960.nodes2969,NodePlus46.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus2960.p2970,GridPlus.atNode 2970,GridPlus.atNode 2971,NodePlus46.w26,CompactPlus2960.checked2970,CompactPlus2960.small2970,CompactPlus2960.nodes2970,NodePlus46.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus2960.p2971,GridPlus.atNode 2971,GridPlus.atNode 2972,NodePlus46.w27,CompactPlus2960.checked2971,CompactPlus2960.small2971,CompactPlus2960.nodes2971,NodePlus46.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus2960.p2972,GridPlus.atNode 2972,GridPlus.atNode 2973,NodePlus46.w28,CompactPlus2960.checked2972,CompactPlus2960.small2972,CompactPlus2960.nodes2972,NodePlus46.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus2960.p2973,GridPlus.atNode 2973,GridPlus.atNode 2974,NodePlus46.w29,CompactPlus2960.checked2973,CompactPlus2960.small2973,CompactPlus2960.nodes2973,NodePlus46.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus2960.p2974,GridPlus.atNode 2974,GridPlus.atNode 2975,NodePlus46.w30,CompactPlus2960.checked2974,CompactPlus2960.small2974,CompactPlus2960.nodes2974,NodePlus46.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus2960.p2975,GridPlus.atNode 2975,GridPlus.atNode 2976,NodePlus46.w31,CompactPlus2960.checked2975,CompactPlus2960.small2975,CompactPlus2960.nodes2975,NodePlus46.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus2976.p2976,GridPlus.atNode 2976,GridPlus.atNode 2977,NodePlus46.w32,CompactPlus2976.checked2976,CompactPlus2976.small2976,CompactPlus2976.nodes2976,NodePlus46.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus2976.p2977,GridPlus.atNode 2977,GridPlus.atNode 2978,NodePlus46.w33,CompactPlus2976.checked2977,CompactPlus2976.small2977,CompactPlus2976.nodes2977,NodePlus46.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus2976.p2978,GridPlus.atNode 2978,GridPlus.atNode 2979,NodePlus46.w34,CompactPlus2976.checked2978,CompactPlus2976.small2978,CompactPlus2976.nodes2978,NodePlus46.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus2976.p2979,GridPlus.atNode 2979,GridPlus.atNode 2980,NodePlus46.w35,CompactPlus2976.checked2979,CompactPlus2976.small2979,CompactPlus2976.nodes2979,NodePlus46.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus2976.p2980,GridPlus.atNode 2980,GridPlus.atNode 2981,NodePlus46.w36,CompactPlus2976.checked2980,CompactPlus2976.small2980,CompactPlus2976.nodes2980,NodePlus46.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus2976.p2981,GridPlus.atNode 2981,GridPlus.atNode 2982,NodePlus46.w37,CompactPlus2976.checked2981,CompactPlus2976.small2981,CompactPlus2976.nodes2981,NodePlus46.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus2976.p2982,GridPlus.atNode 2982,GridPlus.atNode 2983,NodePlus46.w38,CompactPlus2976.checked2982,CompactPlus2976.small2982,CompactPlus2976.nodes2982,NodePlus46.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus2976.p2983,GridPlus.atNode 2983,GridPlus.atNode 2984,NodePlus46.w39,CompactPlus2976.checked2983,CompactPlus2976.small2983,CompactPlus2976.nodes2983,NodePlus46.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus2976.p2984,GridPlus.atNode 2984,GridPlus.atNode 2985,NodePlus46.w40,CompactPlus2976.checked2984,CompactPlus2976.small2984,CompactPlus2976.nodes2984,NodePlus46.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus2976.p2985,GridPlus.atNode 2985,GridPlus.atNode 2986,NodePlus46.w41,CompactPlus2976.checked2985,CompactPlus2976.small2985,CompactPlus2976.nodes2985,NodePlus46.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus2976.p2986,GridPlus.atNode 2986,GridPlus.atNode 2987,NodePlus46.w42,CompactPlus2976.checked2986,CompactPlus2976.small2986,CompactPlus2976.nodes2986,NodePlus46.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus2976.p2987,GridPlus.atNode 2987,GridPlus.atNode 2988,NodePlus46.w43,CompactPlus2976.checked2987,CompactPlus2976.small2987,CompactPlus2976.nodes2987,NodePlus46.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus2976.p2988,GridPlus.atNode 2988,GridPlus.atNode 2989,NodePlus46.w44,CompactPlus2976.checked2988,CompactPlus2976.small2988,CompactPlus2976.nodes2988,NodePlus46.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus2976.p2989,GridPlus.atNode 2989,GridPlus.atNode 2990,NodePlus46.w45,CompactPlus2976.checked2989,CompactPlus2976.small2989,CompactPlus2976.nodes2989,NodePlus46.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus2976.p2990,GridPlus.atNode 2990,GridPlus.atNode 2991,NodePlus46.w46,CompactPlus2976.checked2990,CompactPlus2976.small2990,CompactPlus2976.nodes2990,NodePlus46.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus2976.p2991,GridPlus.atNode 2991,GridPlus.atNode 2992,NodePlus46.w47,CompactPlus2976.checked2991,CompactPlus2976.small2991,CompactPlus2976.nodes2991,NodePlus46.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus2992.p2992,GridPlus.atNode 2992,GridPlus.atNode 2993,NodePlus46.w48,CompactPlus2992.checked2992,CompactPlus2992.small2992,CompactPlus2992.nodes2992,NodePlus46.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus2992.p2993,GridPlus.atNode 2993,GridPlus.atNode 2994,NodePlus46.w49,CompactPlus2992.checked2993,CompactPlus2992.small2993,CompactPlus2992.nodes2993,NodePlus46.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus2992.p2994,GridPlus.atNode 2994,GridPlus.atNode 2995,NodePlus46.w50,CompactPlus2992.checked2994,CompactPlus2992.small2994,CompactPlus2992.nodes2994,NodePlus46.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus2992.p2995,GridPlus.atNode 2995,GridPlus.atNode 2996,NodePlus46.w51,CompactPlus2992.checked2995,CompactPlus2992.small2995,CompactPlus2992.nodes2995,NodePlus46.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus2992.p2996,GridPlus.atNode 2996,GridPlus.atNode 2997,NodePlus46.w52,CompactPlus2992.checked2996,CompactPlus2992.small2996,CompactPlus2992.nodes2996,NodePlus46.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus2992.p2997,GridPlus.atNode 2997,GridPlus.atNode 2998,NodePlus46.w53,CompactPlus2992.checked2997,CompactPlus2992.small2997,CompactPlus2992.nodes2997,NodePlus46.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus2992.p2998,GridPlus.atNode 2998,GridPlus.atNode 2999,NodePlus46.w54,CompactPlus2992.checked2998,CompactPlus2992.small2998,CompactPlus2992.nodes2998,NodePlus46.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus2992.p2999,GridPlus.atNode 2999,GridPlus.atNode 3000,NodePlus46.w55,CompactPlus2992.checked2999,CompactPlus2992.small2999,CompactPlus2992.nodes2999,NodePlus46.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus2992.p3000,GridPlus.atNode 3000,GridPlus.atNode 3001,NodePlus46.w56,CompactPlus2992.checked3000,CompactPlus2992.small3000,CompactPlus2992.nodes3000,NodePlus46.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus2992.p3001,GridPlus.atNode 3001,GridPlus.atNode 3002,NodePlus46.w57,CompactPlus2992.checked3001,CompactPlus2992.small3001,CompactPlus2992.nodes3001,NodePlus46.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus2992.p3002,GridPlus.atNode 3002,GridPlus.atNode 3003,NodePlus46.w58,CompactPlus2992.checked3002,CompactPlus2992.small3002,CompactPlus2992.nodes3002,NodePlus46.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus2992.p3003,GridPlus.atNode 3003,GridPlus.atNode 3004,NodePlus46.w59,CompactPlus2992.checked3003,CompactPlus2992.small3003,CompactPlus2992.nodes3003,NodePlus46.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus2992.p3004,GridPlus.atNode 3004,GridPlus.atNode 3005,NodePlus46.w60,CompactPlus2992.checked3004,CompactPlus2992.small3004,CompactPlus2992.nodes3004,NodePlus46.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus2992.p3005,GridPlus.atNode 3005,GridPlus.atNode 3006,NodePlus46.w61,CompactPlus2992.checked3005,CompactPlus2992.small3005,CompactPlus2992.nodes3005,NodePlus46.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus2992.p3006,GridPlus.atNode 3006,GridPlus.atNode 3007,NodePlus46.w62,CompactPlus2992.checked3006,CompactPlus2992.small3006,CompactPlus2992.nodes3006,NodePlus46.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus2992.p3007,GridPlus.atNode 3007,GridPlus.atNode 3008,NodePlus46.w63,CompactPlus2992.checked3007,CompactPlus2992.small3007,CompactPlus2992.nodes3007,NodePlus46.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (2944+j) ∧
    (atRow j).right=GridPlus.atNode (2944+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus46
