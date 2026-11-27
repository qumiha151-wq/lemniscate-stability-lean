import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus3072
import SolitonClassification.Rotating.ResetPackedPlus3088
import SolitonClassification.Rotating.ResetPackedPlus3104
import SolitonClassification.Rotating.ResetPackedPlus3120
namespace SolitonClassification.Rotating.DyadicReset.TilePlus48
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus3072.p3072,GridPlus.atNode 3072,GridPlus.atNode 3073,NodePlus48.w0,CompactPlus3072.checked3072,CompactPlus3072.small3072,CompactPlus3072.nodes3072,NodePlus48.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus3072.p3073,GridPlus.atNode 3073,GridPlus.atNode 3074,NodePlus48.w1,CompactPlus3072.checked3073,CompactPlus3072.small3073,CompactPlus3072.nodes3073,NodePlus48.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus3072.p3074,GridPlus.atNode 3074,GridPlus.atNode 3075,NodePlus48.w2,CompactPlus3072.checked3074,CompactPlus3072.small3074,CompactPlus3072.nodes3074,NodePlus48.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus3072.p3075,GridPlus.atNode 3075,GridPlus.atNode 3076,NodePlus48.w3,CompactPlus3072.checked3075,CompactPlus3072.small3075,CompactPlus3072.nodes3075,NodePlus48.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus3072.p3076,GridPlus.atNode 3076,GridPlus.atNode 3077,NodePlus48.w4,CompactPlus3072.checked3076,CompactPlus3072.small3076,CompactPlus3072.nodes3076,NodePlus48.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus3072.p3077,GridPlus.atNode 3077,GridPlus.atNode 3078,NodePlus48.w5,CompactPlus3072.checked3077,CompactPlus3072.small3077,CompactPlus3072.nodes3077,NodePlus48.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus3072.p3078,GridPlus.atNode 3078,GridPlus.atNode 3079,NodePlus48.w6,CompactPlus3072.checked3078,CompactPlus3072.small3078,CompactPlus3072.nodes3078,NodePlus48.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus3072.p3079,GridPlus.atNode 3079,GridPlus.atNode 3080,NodePlus48.w7,CompactPlus3072.checked3079,CompactPlus3072.small3079,CompactPlus3072.nodes3079,NodePlus48.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus3072.p3080,GridPlus.atNode 3080,GridPlus.atNode 3081,NodePlus48.w8,CompactPlus3072.checked3080,CompactPlus3072.small3080,CompactPlus3072.nodes3080,NodePlus48.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus3072.p3081,GridPlus.atNode 3081,GridPlus.atNode 3082,NodePlus48.w9,CompactPlus3072.checked3081,CompactPlus3072.small3081,CompactPlus3072.nodes3081,NodePlus48.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus3072.p3082,GridPlus.atNode 3082,GridPlus.atNode 3083,NodePlus48.w10,CompactPlus3072.checked3082,CompactPlus3072.small3082,CompactPlus3072.nodes3082,NodePlus48.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus3072.p3083,GridPlus.atNode 3083,GridPlus.atNode 3084,NodePlus48.w11,CompactPlus3072.checked3083,CompactPlus3072.small3083,CompactPlus3072.nodes3083,NodePlus48.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus3072.p3084,GridPlus.atNode 3084,GridPlus.atNode 3085,NodePlus48.w12,CompactPlus3072.checked3084,CompactPlus3072.small3084,CompactPlus3072.nodes3084,NodePlus48.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus3072.p3085,GridPlus.atNode 3085,GridPlus.atNode 3086,NodePlus48.w13,CompactPlus3072.checked3085,CompactPlus3072.small3085,CompactPlus3072.nodes3085,NodePlus48.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus3072.p3086,GridPlus.atNode 3086,GridPlus.atNode 3087,NodePlus48.w14,CompactPlus3072.checked3086,CompactPlus3072.small3086,CompactPlus3072.nodes3086,NodePlus48.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus3072.p3087,GridPlus.atNode 3087,GridPlus.atNode 3088,NodePlus48.w15,CompactPlus3072.checked3087,CompactPlus3072.small3087,CompactPlus3072.nodes3087,NodePlus48.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus3088.p3088,GridPlus.atNode 3088,GridPlus.atNode 3089,NodePlus48.w16,CompactPlus3088.checked3088,CompactPlus3088.small3088,CompactPlus3088.nodes3088,NodePlus48.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus3088.p3089,GridPlus.atNode 3089,GridPlus.atNode 3090,NodePlus48.w17,CompactPlus3088.checked3089,CompactPlus3088.small3089,CompactPlus3088.nodes3089,NodePlus48.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus3088.p3090,GridPlus.atNode 3090,GridPlus.atNode 3091,NodePlus48.w18,CompactPlus3088.checked3090,CompactPlus3088.small3090,CompactPlus3088.nodes3090,NodePlus48.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus3088.p3091,GridPlus.atNode 3091,GridPlus.atNode 3092,NodePlus48.w19,CompactPlus3088.checked3091,CompactPlus3088.small3091,CompactPlus3088.nodes3091,NodePlus48.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus3088.p3092,GridPlus.atNode 3092,GridPlus.atNode 3093,NodePlus48.w20,CompactPlus3088.checked3092,CompactPlus3088.small3092,CompactPlus3088.nodes3092,NodePlus48.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus3088.p3093,GridPlus.atNode 3093,GridPlus.atNode 3094,NodePlus48.w21,CompactPlus3088.checked3093,CompactPlus3088.small3093,CompactPlus3088.nodes3093,NodePlus48.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus3088.p3094,GridPlus.atNode 3094,GridPlus.atNode 3095,NodePlus48.w22,CompactPlus3088.checked3094,CompactPlus3088.small3094,CompactPlus3088.nodes3094,NodePlus48.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus3088.p3095,GridPlus.atNode 3095,GridPlus.atNode 3096,NodePlus48.w23,CompactPlus3088.checked3095,CompactPlus3088.small3095,CompactPlus3088.nodes3095,NodePlus48.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus3088.p3096,GridPlus.atNode 3096,GridPlus.atNode 3097,NodePlus48.w24,CompactPlus3088.checked3096,CompactPlus3088.small3096,CompactPlus3088.nodes3096,NodePlus48.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus3088.p3097,GridPlus.atNode 3097,GridPlus.atNode 3098,NodePlus48.w25,CompactPlus3088.checked3097,CompactPlus3088.small3097,CompactPlus3088.nodes3097,NodePlus48.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus3088.p3098,GridPlus.atNode 3098,GridPlus.atNode 3099,NodePlus48.w26,CompactPlus3088.checked3098,CompactPlus3088.small3098,CompactPlus3088.nodes3098,NodePlus48.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus3088.p3099,GridPlus.atNode 3099,GridPlus.atNode 3100,NodePlus48.w27,CompactPlus3088.checked3099,CompactPlus3088.small3099,CompactPlus3088.nodes3099,NodePlus48.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus3088.p3100,GridPlus.atNode 3100,GridPlus.atNode 3101,NodePlus48.w28,CompactPlus3088.checked3100,CompactPlus3088.small3100,CompactPlus3088.nodes3100,NodePlus48.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus3088.p3101,GridPlus.atNode 3101,GridPlus.atNode 3102,NodePlus48.w29,CompactPlus3088.checked3101,CompactPlus3088.small3101,CompactPlus3088.nodes3101,NodePlus48.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus3088.p3102,GridPlus.atNode 3102,GridPlus.atNode 3103,NodePlus48.w30,CompactPlus3088.checked3102,CompactPlus3088.small3102,CompactPlus3088.nodes3102,NodePlus48.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus3088.p3103,GridPlus.atNode 3103,GridPlus.atNode 3104,NodePlus48.w31,CompactPlus3088.checked3103,CompactPlus3088.small3103,CompactPlus3088.nodes3103,NodePlus48.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus3104.p3104,GridPlus.atNode 3104,GridPlus.atNode 3105,NodePlus48.w32,CompactPlus3104.checked3104,CompactPlus3104.small3104,CompactPlus3104.nodes3104,NodePlus48.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus3104.p3105,GridPlus.atNode 3105,GridPlus.atNode 3106,NodePlus48.w33,CompactPlus3104.checked3105,CompactPlus3104.small3105,CompactPlus3104.nodes3105,NodePlus48.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus3104.p3106,GridPlus.atNode 3106,GridPlus.atNode 3107,NodePlus48.w34,CompactPlus3104.checked3106,CompactPlus3104.small3106,CompactPlus3104.nodes3106,NodePlus48.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus3104.p3107,GridPlus.atNode 3107,GridPlus.atNode 3108,NodePlus48.w35,CompactPlus3104.checked3107,CompactPlus3104.small3107,CompactPlus3104.nodes3107,NodePlus48.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus3104.p3108,GridPlus.atNode 3108,GridPlus.atNode 3109,NodePlus48.w36,CompactPlus3104.checked3108,CompactPlus3104.small3108,CompactPlus3104.nodes3108,NodePlus48.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus3104.p3109,GridPlus.atNode 3109,GridPlus.atNode 3110,NodePlus48.w37,CompactPlus3104.checked3109,CompactPlus3104.small3109,CompactPlus3104.nodes3109,NodePlus48.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus3104.p3110,GridPlus.atNode 3110,GridPlus.atNode 3111,NodePlus48.w38,CompactPlus3104.checked3110,CompactPlus3104.small3110,CompactPlus3104.nodes3110,NodePlus48.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus3104.p3111,GridPlus.atNode 3111,GridPlus.atNode 3112,NodePlus48.w39,CompactPlus3104.checked3111,CompactPlus3104.small3111,CompactPlus3104.nodes3111,NodePlus48.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus3104.p3112,GridPlus.atNode 3112,GridPlus.atNode 3113,NodePlus48.w40,CompactPlus3104.checked3112,CompactPlus3104.small3112,CompactPlus3104.nodes3112,NodePlus48.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus3104.p3113,GridPlus.atNode 3113,GridPlus.atNode 3114,NodePlus48.w41,CompactPlus3104.checked3113,CompactPlus3104.small3113,CompactPlus3104.nodes3113,NodePlus48.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus3104.p3114,GridPlus.atNode 3114,GridPlus.atNode 3115,NodePlus48.w42,CompactPlus3104.checked3114,CompactPlus3104.small3114,CompactPlus3104.nodes3114,NodePlus48.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus3104.p3115,GridPlus.atNode 3115,GridPlus.atNode 3116,NodePlus48.w43,CompactPlus3104.checked3115,CompactPlus3104.small3115,CompactPlus3104.nodes3115,NodePlus48.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus3104.p3116,GridPlus.atNode 3116,GridPlus.atNode 3117,NodePlus48.w44,CompactPlus3104.checked3116,CompactPlus3104.small3116,CompactPlus3104.nodes3116,NodePlus48.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus3104.p3117,GridPlus.atNode 3117,GridPlus.atNode 3118,NodePlus48.w45,CompactPlus3104.checked3117,CompactPlus3104.small3117,CompactPlus3104.nodes3117,NodePlus48.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus3104.p3118,GridPlus.atNode 3118,GridPlus.atNode 3119,NodePlus48.w46,CompactPlus3104.checked3118,CompactPlus3104.small3118,CompactPlus3104.nodes3118,NodePlus48.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus3104.p3119,GridPlus.atNode 3119,GridPlus.atNode 3120,NodePlus48.w47,CompactPlus3104.checked3119,CompactPlus3104.small3119,CompactPlus3104.nodes3119,NodePlus48.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus3120.p3120,GridPlus.atNode 3120,GridPlus.atNode 3121,NodePlus48.w48,CompactPlus3120.checked3120,CompactPlus3120.small3120,CompactPlus3120.nodes3120,NodePlus48.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus3120.p3121,GridPlus.atNode 3121,GridPlus.atNode 3122,NodePlus48.w49,CompactPlus3120.checked3121,CompactPlus3120.small3121,CompactPlus3120.nodes3121,NodePlus48.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus3120.p3122,GridPlus.atNode 3122,GridPlus.atNode 3123,NodePlus48.w50,CompactPlus3120.checked3122,CompactPlus3120.small3122,CompactPlus3120.nodes3122,NodePlus48.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus3120.p3123,GridPlus.atNode 3123,GridPlus.atNode 3124,NodePlus48.w51,CompactPlus3120.checked3123,CompactPlus3120.small3123,CompactPlus3120.nodes3123,NodePlus48.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus3120.p3124,GridPlus.atNode 3124,GridPlus.atNode 3125,NodePlus48.w52,CompactPlus3120.checked3124,CompactPlus3120.small3124,CompactPlus3120.nodes3124,NodePlus48.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus3120.p3125,GridPlus.atNode 3125,GridPlus.atNode 3126,NodePlus48.w53,CompactPlus3120.checked3125,CompactPlus3120.small3125,CompactPlus3120.nodes3125,NodePlus48.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus3120.p3126,GridPlus.atNode 3126,GridPlus.atNode 3127,NodePlus48.w54,CompactPlus3120.checked3126,CompactPlus3120.small3126,CompactPlus3120.nodes3126,NodePlus48.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus3120.p3127,GridPlus.atNode 3127,GridPlus.atNode 3128,NodePlus48.w55,CompactPlus3120.checked3127,CompactPlus3120.small3127,CompactPlus3120.nodes3127,NodePlus48.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus3120.p3128,GridPlus.atNode 3128,GridPlus.atNode 3129,NodePlus48.w56,CompactPlus3120.checked3128,CompactPlus3120.small3128,CompactPlus3120.nodes3128,NodePlus48.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus3120.p3129,GridPlus.atNode 3129,GridPlus.atNode 3130,NodePlus48.w57,CompactPlus3120.checked3129,CompactPlus3120.small3129,CompactPlus3120.nodes3129,NodePlus48.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus3120.p3130,GridPlus.atNode 3130,GridPlus.atNode 3131,NodePlus48.w58,CompactPlus3120.checked3130,CompactPlus3120.small3130,CompactPlus3120.nodes3130,NodePlus48.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus3120.p3131,GridPlus.atNode 3131,GridPlus.atNode 3132,NodePlus48.w59,CompactPlus3120.checked3131,CompactPlus3120.small3131,CompactPlus3120.nodes3131,NodePlus48.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus3120.p3132,GridPlus.atNode 3132,GridPlus.atNode 3133,NodePlus48.w60,CompactPlus3120.checked3132,CompactPlus3120.small3132,CompactPlus3120.nodes3132,NodePlus48.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus3120.p3133,GridPlus.atNode 3133,GridPlus.atNode 3134,NodePlus48.w61,CompactPlus3120.checked3133,CompactPlus3120.small3133,CompactPlus3120.nodes3133,NodePlus48.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus3120.p3134,GridPlus.atNode 3134,GridPlus.atNode 3135,NodePlus48.w62,CompactPlus3120.checked3134,CompactPlus3120.small3134,CompactPlus3120.nodes3134,NodePlus48.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus3120.p3135,GridPlus.atNode 3135,GridPlus.atNode 3136,NodePlus48.w63,CompactPlus3120.checked3135,CompactPlus3120.small3135,CompactPlus3120.nodes3135,NodePlus48.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (3072+j) ∧
    (atRow j).right=GridPlus.atNode (3072+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus48
