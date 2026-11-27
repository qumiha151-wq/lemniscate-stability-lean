import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus3072
import SolitonClassification.Rotating.ResetPackedMinus3088
import SolitonClassification.Rotating.ResetPackedMinus3104
import SolitonClassification.Rotating.ResetPackedMinus3120
namespace SolitonClassification.Rotating.DyadicReset.TileMinus48
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3072.p3072,GridMinus.atNode 3072,GridMinus.atNode 3073,NodeMinus48.w0,CompactMinus3072.checked3072,CompactMinus3072.small3072,CompactMinus3072.nodes3072,NodeMinus48.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3072.p3073,GridMinus.atNode 3073,GridMinus.atNode 3074,NodeMinus48.w1,CompactMinus3072.checked3073,CompactMinus3072.small3073,CompactMinus3072.nodes3073,NodeMinus48.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3072.p3074,GridMinus.atNode 3074,GridMinus.atNode 3075,NodeMinus48.w2,CompactMinus3072.checked3074,CompactMinus3072.small3074,CompactMinus3072.nodes3074,NodeMinus48.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3072.p3075,GridMinus.atNode 3075,GridMinus.atNode 3076,NodeMinus48.w3,CompactMinus3072.checked3075,CompactMinus3072.small3075,CompactMinus3072.nodes3075,NodeMinus48.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3072.p3076,GridMinus.atNode 3076,GridMinus.atNode 3077,NodeMinus48.w4,CompactMinus3072.checked3076,CompactMinus3072.small3076,CompactMinus3072.nodes3076,NodeMinus48.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3072.p3077,GridMinus.atNode 3077,GridMinus.atNode 3078,NodeMinus48.w5,CompactMinus3072.checked3077,CompactMinus3072.small3077,CompactMinus3072.nodes3077,NodeMinus48.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3072.p3078,GridMinus.atNode 3078,GridMinus.atNode 3079,NodeMinus48.w6,CompactMinus3072.checked3078,CompactMinus3072.small3078,CompactMinus3072.nodes3078,NodeMinus48.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3072.p3079,GridMinus.atNode 3079,GridMinus.atNode 3080,NodeMinus48.w7,CompactMinus3072.checked3079,CompactMinus3072.small3079,CompactMinus3072.nodes3079,NodeMinus48.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3072.p3080,GridMinus.atNode 3080,GridMinus.atNode 3081,NodeMinus48.w8,CompactMinus3072.checked3080,CompactMinus3072.small3080,CompactMinus3072.nodes3080,NodeMinus48.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3072.p3081,GridMinus.atNode 3081,GridMinus.atNode 3082,NodeMinus48.w9,CompactMinus3072.checked3081,CompactMinus3072.small3081,CompactMinus3072.nodes3081,NodeMinus48.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3072.p3082,GridMinus.atNode 3082,GridMinus.atNode 3083,NodeMinus48.w10,CompactMinus3072.checked3082,CompactMinus3072.small3082,CompactMinus3072.nodes3082,NodeMinus48.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3072.p3083,GridMinus.atNode 3083,GridMinus.atNode 3084,NodeMinus48.w11,CompactMinus3072.checked3083,CompactMinus3072.small3083,CompactMinus3072.nodes3083,NodeMinus48.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3072.p3084,GridMinus.atNode 3084,GridMinus.atNode 3085,NodeMinus48.w12,CompactMinus3072.checked3084,CompactMinus3072.small3084,CompactMinus3072.nodes3084,NodeMinus48.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3072.p3085,GridMinus.atNode 3085,GridMinus.atNode 3086,NodeMinus48.w13,CompactMinus3072.checked3085,CompactMinus3072.small3085,CompactMinus3072.nodes3085,NodeMinus48.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3072.p3086,GridMinus.atNode 3086,GridMinus.atNode 3087,NodeMinus48.w14,CompactMinus3072.checked3086,CompactMinus3072.small3086,CompactMinus3072.nodes3086,NodeMinus48.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3072.p3087,GridMinus.atNode 3087,GridMinus.atNode 3088,NodeMinus48.w15,CompactMinus3072.checked3087,CompactMinus3072.small3087,CompactMinus3072.nodes3087,NodeMinus48.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3088.p3088,GridMinus.atNode 3088,GridMinus.atNode 3089,NodeMinus48.w16,CompactMinus3088.checked3088,CompactMinus3088.small3088,CompactMinus3088.nodes3088,NodeMinus48.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3088.p3089,GridMinus.atNode 3089,GridMinus.atNode 3090,NodeMinus48.w17,CompactMinus3088.checked3089,CompactMinus3088.small3089,CompactMinus3088.nodes3089,NodeMinus48.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3088.p3090,GridMinus.atNode 3090,GridMinus.atNode 3091,NodeMinus48.w18,CompactMinus3088.checked3090,CompactMinus3088.small3090,CompactMinus3088.nodes3090,NodeMinus48.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3088.p3091,GridMinus.atNode 3091,GridMinus.atNode 3092,NodeMinus48.w19,CompactMinus3088.checked3091,CompactMinus3088.small3091,CompactMinus3088.nodes3091,NodeMinus48.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3088.p3092,GridMinus.atNode 3092,GridMinus.atNode 3093,NodeMinus48.w20,CompactMinus3088.checked3092,CompactMinus3088.small3092,CompactMinus3088.nodes3092,NodeMinus48.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3088.p3093,GridMinus.atNode 3093,GridMinus.atNode 3094,NodeMinus48.w21,CompactMinus3088.checked3093,CompactMinus3088.small3093,CompactMinus3088.nodes3093,NodeMinus48.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3088.p3094,GridMinus.atNode 3094,GridMinus.atNode 3095,NodeMinus48.w22,CompactMinus3088.checked3094,CompactMinus3088.small3094,CompactMinus3088.nodes3094,NodeMinus48.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3088.p3095,GridMinus.atNode 3095,GridMinus.atNode 3096,NodeMinus48.w23,CompactMinus3088.checked3095,CompactMinus3088.small3095,CompactMinus3088.nodes3095,NodeMinus48.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3088.p3096,GridMinus.atNode 3096,GridMinus.atNode 3097,NodeMinus48.w24,CompactMinus3088.checked3096,CompactMinus3088.small3096,CompactMinus3088.nodes3096,NodeMinus48.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3088.p3097,GridMinus.atNode 3097,GridMinus.atNode 3098,NodeMinus48.w25,CompactMinus3088.checked3097,CompactMinus3088.small3097,CompactMinus3088.nodes3097,NodeMinus48.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3088.p3098,GridMinus.atNode 3098,GridMinus.atNode 3099,NodeMinus48.w26,CompactMinus3088.checked3098,CompactMinus3088.small3098,CompactMinus3088.nodes3098,NodeMinus48.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3088.p3099,GridMinus.atNode 3099,GridMinus.atNode 3100,NodeMinus48.w27,CompactMinus3088.checked3099,CompactMinus3088.small3099,CompactMinus3088.nodes3099,NodeMinus48.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3088.p3100,GridMinus.atNode 3100,GridMinus.atNode 3101,NodeMinus48.w28,CompactMinus3088.checked3100,CompactMinus3088.small3100,CompactMinus3088.nodes3100,NodeMinus48.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3088.p3101,GridMinus.atNode 3101,GridMinus.atNode 3102,NodeMinus48.w29,CompactMinus3088.checked3101,CompactMinus3088.small3101,CompactMinus3088.nodes3101,NodeMinus48.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3088.p3102,GridMinus.atNode 3102,GridMinus.atNode 3103,NodeMinus48.w30,CompactMinus3088.checked3102,CompactMinus3088.small3102,CompactMinus3088.nodes3102,NodeMinus48.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3088.p3103,GridMinus.atNode 3103,GridMinus.atNode 3104,NodeMinus48.w31,CompactMinus3088.checked3103,CompactMinus3088.small3103,CompactMinus3088.nodes3103,NodeMinus48.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3104.p3104,GridMinus.atNode 3104,GridMinus.atNode 3105,NodeMinus48.w32,CompactMinus3104.checked3104,CompactMinus3104.small3104,CompactMinus3104.nodes3104,NodeMinus48.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3104.p3105,GridMinus.atNode 3105,GridMinus.atNode 3106,NodeMinus48.w33,CompactMinus3104.checked3105,CompactMinus3104.small3105,CompactMinus3104.nodes3105,NodeMinus48.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3104.p3106,GridMinus.atNode 3106,GridMinus.atNode 3107,NodeMinus48.w34,CompactMinus3104.checked3106,CompactMinus3104.small3106,CompactMinus3104.nodes3106,NodeMinus48.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3104.p3107,GridMinus.atNode 3107,GridMinus.atNode 3108,NodeMinus48.w35,CompactMinus3104.checked3107,CompactMinus3104.small3107,CompactMinus3104.nodes3107,NodeMinus48.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3104.p3108,GridMinus.atNode 3108,GridMinus.atNode 3109,NodeMinus48.w36,CompactMinus3104.checked3108,CompactMinus3104.small3108,CompactMinus3104.nodes3108,NodeMinus48.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3104.p3109,GridMinus.atNode 3109,GridMinus.atNode 3110,NodeMinus48.w37,CompactMinus3104.checked3109,CompactMinus3104.small3109,CompactMinus3104.nodes3109,NodeMinus48.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3104.p3110,GridMinus.atNode 3110,GridMinus.atNode 3111,NodeMinus48.w38,CompactMinus3104.checked3110,CompactMinus3104.small3110,CompactMinus3104.nodes3110,NodeMinus48.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3104.p3111,GridMinus.atNode 3111,GridMinus.atNode 3112,NodeMinus48.w39,CompactMinus3104.checked3111,CompactMinus3104.small3111,CompactMinus3104.nodes3111,NodeMinus48.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3104.p3112,GridMinus.atNode 3112,GridMinus.atNode 3113,NodeMinus48.w40,CompactMinus3104.checked3112,CompactMinus3104.small3112,CompactMinus3104.nodes3112,NodeMinus48.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3104.p3113,GridMinus.atNode 3113,GridMinus.atNode 3114,NodeMinus48.w41,CompactMinus3104.checked3113,CompactMinus3104.small3113,CompactMinus3104.nodes3113,NodeMinus48.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3104.p3114,GridMinus.atNode 3114,GridMinus.atNode 3115,NodeMinus48.w42,CompactMinus3104.checked3114,CompactMinus3104.small3114,CompactMinus3104.nodes3114,NodeMinus48.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3104.p3115,GridMinus.atNode 3115,GridMinus.atNode 3116,NodeMinus48.w43,CompactMinus3104.checked3115,CompactMinus3104.small3115,CompactMinus3104.nodes3115,NodeMinus48.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3104.p3116,GridMinus.atNode 3116,GridMinus.atNode 3117,NodeMinus48.w44,CompactMinus3104.checked3116,CompactMinus3104.small3116,CompactMinus3104.nodes3116,NodeMinus48.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3104.p3117,GridMinus.atNode 3117,GridMinus.atNode 3118,NodeMinus48.w45,CompactMinus3104.checked3117,CompactMinus3104.small3117,CompactMinus3104.nodes3117,NodeMinus48.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3104.p3118,GridMinus.atNode 3118,GridMinus.atNode 3119,NodeMinus48.w46,CompactMinus3104.checked3118,CompactMinus3104.small3118,CompactMinus3104.nodes3118,NodeMinus48.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3104.p3119,GridMinus.atNode 3119,GridMinus.atNode 3120,NodeMinus48.w47,CompactMinus3104.checked3119,CompactMinus3104.small3119,CompactMinus3104.nodes3119,NodeMinus48.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3120.p3120,GridMinus.atNode 3120,GridMinus.atNode 3121,NodeMinus48.w48,CompactMinus3120.checked3120,CompactMinus3120.small3120,CompactMinus3120.nodes3120,NodeMinus48.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3120.p3121,GridMinus.atNode 3121,GridMinus.atNode 3122,NodeMinus48.w49,CompactMinus3120.checked3121,CompactMinus3120.small3121,CompactMinus3120.nodes3121,NodeMinus48.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3120.p3122,GridMinus.atNode 3122,GridMinus.atNode 3123,NodeMinus48.w50,CompactMinus3120.checked3122,CompactMinus3120.small3122,CompactMinus3120.nodes3122,NodeMinus48.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3120.p3123,GridMinus.atNode 3123,GridMinus.atNode 3124,NodeMinus48.w51,CompactMinus3120.checked3123,CompactMinus3120.small3123,CompactMinus3120.nodes3123,NodeMinus48.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3120.p3124,GridMinus.atNode 3124,GridMinus.atNode 3125,NodeMinus48.w52,CompactMinus3120.checked3124,CompactMinus3120.small3124,CompactMinus3120.nodes3124,NodeMinus48.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3120.p3125,GridMinus.atNode 3125,GridMinus.atNode 3126,NodeMinus48.w53,CompactMinus3120.checked3125,CompactMinus3120.small3125,CompactMinus3120.nodes3125,NodeMinus48.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3120.p3126,GridMinus.atNode 3126,GridMinus.atNode 3127,NodeMinus48.w54,CompactMinus3120.checked3126,CompactMinus3120.small3126,CompactMinus3120.nodes3126,NodeMinus48.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3120.p3127,GridMinus.atNode 3127,GridMinus.atNode 3128,NodeMinus48.w55,CompactMinus3120.checked3127,CompactMinus3120.small3127,CompactMinus3120.nodes3127,NodeMinus48.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3120.p3128,GridMinus.atNode 3128,GridMinus.atNode 3129,NodeMinus48.w56,CompactMinus3120.checked3128,CompactMinus3120.small3128,CompactMinus3120.nodes3128,NodeMinus48.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3120.p3129,GridMinus.atNode 3129,GridMinus.atNode 3130,NodeMinus48.w57,CompactMinus3120.checked3129,CompactMinus3120.small3129,CompactMinus3120.nodes3129,NodeMinus48.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3120.p3130,GridMinus.atNode 3130,GridMinus.atNode 3131,NodeMinus48.w58,CompactMinus3120.checked3130,CompactMinus3120.small3130,CompactMinus3120.nodes3130,NodeMinus48.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3120.p3131,GridMinus.atNode 3131,GridMinus.atNode 3132,NodeMinus48.w59,CompactMinus3120.checked3131,CompactMinus3120.small3131,CompactMinus3120.nodes3131,NodeMinus48.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3120.p3132,GridMinus.atNode 3132,GridMinus.atNode 3133,NodeMinus48.w60,CompactMinus3120.checked3132,CompactMinus3120.small3132,CompactMinus3120.nodes3132,NodeMinus48.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3120.p3133,GridMinus.atNode 3133,GridMinus.atNode 3134,NodeMinus48.w61,CompactMinus3120.checked3133,CompactMinus3120.small3133,CompactMinus3120.nodes3133,NodeMinus48.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3120.p3134,GridMinus.atNode 3134,GridMinus.atNode 3135,NodeMinus48.w62,CompactMinus3120.checked3134,CompactMinus3120.small3134,CompactMinus3120.nodes3134,NodeMinus48.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3120.p3135,GridMinus.atNode 3135,GridMinus.atNode 3136,NodeMinus48.w63,CompactMinus3120.checked3135,CompactMinus3120.small3135,CompactMinus3120.nodes3135,NodeMinus48.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (3072+j) ∧
    (atRow j).right=GridMinus.atNode (3072+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus48
