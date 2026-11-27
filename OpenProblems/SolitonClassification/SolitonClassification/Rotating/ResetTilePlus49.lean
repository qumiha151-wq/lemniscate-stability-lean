import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus3136
import SolitonClassification.Rotating.ResetPackedPlus3152
import SolitonClassification.Rotating.ResetPackedPlus3168
import SolitonClassification.Rotating.ResetPackedPlus3184
namespace SolitonClassification.Rotating.DyadicReset.TilePlus49
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus3136.p3136,GridPlus.atNode 3136,GridPlus.atNode 3137,NodePlus49.w0,CompactPlus3136.checked3136,CompactPlus3136.small3136,CompactPlus3136.nodes3136,NodePlus49.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus3136.p3137,GridPlus.atNode 3137,GridPlus.atNode 3138,NodePlus49.w1,CompactPlus3136.checked3137,CompactPlus3136.small3137,CompactPlus3136.nodes3137,NodePlus49.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus3136.p3138,GridPlus.atNode 3138,GridPlus.atNode 3139,NodePlus49.w2,CompactPlus3136.checked3138,CompactPlus3136.small3138,CompactPlus3136.nodes3138,NodePlus49.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus3136.p3139,GridPlus.atNode 3139,GridPlus.atNode 3140,NodePlus49.w3,CompactPlus3136.checked3139,CompactPlus3136.small3139,CompactPlus3136.nodes3139,NodePlus49.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus3136.p3140,GridPlus.atNode 3140,GridPlus.atNode 3141,NodePlus49.w4,CompactPlus3136.checked3140,CompactPlus3136.small3140,CompactPlus3136.nodes3140,NodePlus49.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus3136.p3141,GridPlus.atNode 3141,GridPlus.atNode 3142,NodePlus49.w5,CompactPlus3136.checked3141,CompactPlus3136.small3141,CompactPlus3136.nodes3141,NodePlus49.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus3136.p3142,GridPlus.atNode 3142,GridPlus.atNode 3143,NodePlus49.w6,CompactPlus3136.checked3142,CompactPlus3136.small3142,CompactPlus3136.nodes3142,NodePlus49.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus3136.p3143,GridPlus.atNode 3143,GridPlus.atNode 3144,NodePlus49.w7,CompactPlus3136.checked3143,CompactPlus3136.small3143,CompactPlus3136.nodes3143,NodePlus49.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus3136.p3144,GridPlus.atNode 3144,GridPlus.atNode 3145,NodePlus49.w8,CompactPlus3136.checked3144,CompactPlus3136.small3144,CompactPlus3136.nodes3144,NodePlus49.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus3136.p3145,GridPlus.atNode 3145,GridPlus.atNode 3146,NodePlus49.w9,CompactPlus3136.checked3145,CompactPlus3136.small3145,CompactPlus3136.nodes3145,NodePlus49.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus3136.p3146,GridPlus.atNode 3146,GridPlus.atNode 3147,NodePlus49.w10,CompactPlus3136.checked3146,CompactPlus3136.small3146,CompactPlus3136.nodes3146,NodePlus49.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus3136.p3147,GridPlus.atNode 3147,GridPlus.atNode 3148,NodePlus49.w11,CompactPlus3136.checked3147,CompactPlus3136.small3147,CompactPlus3136.nodes3147,NodePlus49.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus3136.p3148,GridPlus.atNode 3148,GridPlus.atNode 3149,NodePlus49.w12,CompactPlus3136.checked3148,CompactPlus3136.small3148,CompactPlus3136.nodes3148,NodePlus49.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus3136.p3149,GridPlus.atNode 3149,GridPlus.atNode 3150,NodePlus49.w13,CompactPlus3136.checked3149,CompactPlus3136.small3149,CompactPlus3136.nodes3149,NodePlus49.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus3136.p3150,GridPlus.atNode 3150,GridPlus.atNode 3151,NodePlus49.w14,CompactPlus3136.checked3150,CompactPlus3136.small3150,CompactPlus3136.nodes3150,NodePlus49.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus3136.p3151,GridPlus.atNode 3151,GridPlus.atNode 3152,NodePlus49.w15,CompactPlus3136.checked3151,CompactPlus3136.small3151,CompactPlus3136.nodes3151,NodePlus49.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus3152.p3152,GridPlus.atNode 3152,GridPlus.atNode 3153,NodePlus49.w16,CompactPlus3152.checked3152,CompactPlus3152.small3152,CompactPlus3152.nodes3152,NodePlus49.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus3152.p3153,GridPlus.atNode 3153,GridPlus.atNode 3154,NodePlus49.w17,CompactPlus3152.checked3153,CompactPlus3152.small3153,CompactPlus3152.nodes3153,NodePlus49.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus3152.p3154,GridPlus.atNode 3154,GridPlus.atNode 3155,NodePlus49.w18,CompactPlus3152.checked3154,CompactPlus3152.small3154,CompactPlus3152.nodes3154,NodePlus49.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus3152.p3155,GridPlus.atNode 3155,GridPlus.atNode 3156,NodePlus49.w19,CompactPlus3152.checked3155,CompactPlus3152.small3155,CompactPlus3152.nodes3155,NodePlus49.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus3152.p3156,GridPlus.atNode 3156,GridPlus.atNode 3157,NodePlus49.w20,CompactPlus3152.checked3156,CompactPlus3152.small3156,CompactPlus3152.nodes3156,NodePlus49.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus3152.p3157,GridPlus.atNode 3157,GridPlus.atNode 3158,NodePlus49.w21,CompactPlus3152.checked3157,CompactPlus3152.small3157,CompactPlus3152.nodes3157,NodePlus49.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus3152.p3158,GridPlus.atNode 3158,GridPlus.atNode 3159,NodePlus49.w22,CompactPlus3152.checked3158,CompactPlus3152.small3158,CompactPlus3152.nodes3158,NodePlus49.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus3152.p3159,GridPlus.atNode 3159,GridPlus.atNode 3160,NodePlus49.w23,CompactPlus3152.checked3159,CompactPlus3152.small3159,CompactPlus3152.nodes3159,NodePlus49.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus3152.p3160,GridPlus.atNode 3160,GridPlus.atNode 3161,NodePlus49.w24,CompactPlus3152.checked3160,CompactPlus3152.small3160,CompactPlus3152.nodes3160,NodePlus49.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus3152.p3161,GridPlus.atNode 3161,GridPlus.atNode 3162,NodePlus49.w25,CompactPlus3152.checked3161,CompactPlus3152.small3161,CompactPlus3152.nodes3161,NodePlus49.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus3152.p3162,GridPlus.atNode 3162,GridPlus.atNode 3163,NodePlus49.w26,CompactPlus3152.checked3162,CompactPlus3152.small3162,CompactPlus3152.nodes3162,NodePlus49.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus3152.p3163,GridPlus.atNode 3163,GridPlus.atNode 3164,NodePlus49.w27,CompactPlus3152.checked3163,CompactPlus3152.small3163,CompactPlus3152.nodes3163,NodePlus49.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus3152.p3164,GridPlus.atNode 3164,GridPlus.atNode 3165,NodePlus49.w28,CompactPlus3152.checked3164,CompactPlus3152.small3164,CompactPlus3152.nodes3164,NodePlus49.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus3152.p3165,GridPlus.atNode 3165,GridPlus.atNode 3166,NodePlus49.w29,CompactPlus3152.checked3165,CompactPlus3152.small3165,CompactPlus3152.nodes3165,NodePlus49.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus3152.p3166,GridPlus.atNode 3166,GridPlus.atNode 3167,NodePlus49.w30,CompactPlus3152.checked3166,CompactPlus3152.small3166,CompactPlus3152.nodes3166,NodePlus49.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus3152.p3167,GridPlus.atNode 3167,GridPlus.atNode 3168,NodePlus49.w31,CompactPlus3152.checked3167,CompactPlus3152.small3167,CompactPlus3152.nodes3167,NodePlus49.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus3168.p3168,GridPlus.atNode 3168,GridPlus.atNode 3169,NodePlus49.w32,CompactPlus3168.checked3168,CompactPlus3168.small3168,CompactPlus3168.nodes3168,NodePlus49.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus3168.p3169,GridPlus.atNode 3169,GridPlus.atNode 3170,NodePlus49.w33,CompactPlus3168.checked3169,CompactPlus3168.small3169,CompactPlus3168.nodes3169,NodePlus49.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus3168.p3170,GridPlus.atNode 3170,GridPlus.atNode 3171,NodePlus49.w34,CompactPlus3168.checked3170,CompactPlus3168.small3170,CompactPlus3168.nodes3170,NodePlus49.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus3168.p3171,GridPlus.atNode 3171,GridPlus.atNode 3172,NodePlus49.w35,CompactPlus3168.checked3171,CompactPlus3168.small3171,CompactPlus3168.nodes3171,NodePlus49.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus3168.p3172,GridPlus.atNode 3172,GridPlus.atNode 3173,NodePlus49.w36,CompactPlus3168.checked3172,CompactPlus3168.small3172,CompactPlus3168.nodes3172,NodePlus49.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus3168.p3173,GridPlus.atNode 3173,GridPlus.atNode 3174,NodePlus49.w37,CompactPlus3168.checked3173,CompactPlus3168.small3173,CompactPlus3168.nodes3173,NodePlus49.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus3168.p3174,GridPlus.atNode 3174,GridPlus.atNode 3175,NodePlus49.w38,CompactPlus3168.checked3174,CompactPlus3168.small3174,CompactPlus3168.nodes3174,NodePlus49.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus3168.p3175,GridPlus.atNode 3175,GridPlus.atNode 3176,NodePlus49.w39,CompactPlus3168.checked3175,CompactPlus3168.small3175,CompactPlus3168.nodes3175,NodePlus49.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus3168.p3176,GridPlus.atNode 3176,GridPlus.atNode 3177,NodePlus49.w40,CompactPlus3168.checked3176,CompactPlus3168.small3176,CompactPlus3168.nodes3176,NodePlus49.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus3168.p3177,GridPlus.atNode 3177,GridPlus.atNode 3178,NodePlus49.w41,CompactPlus3168.checked3177,CompactPlus3168.small3177,CompactPlus3168.nodes3177,NodePlus49.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus3168.p3178,GridPlus.atNode 3178,GridPlus.atNode 3179,NodePlus49.w42,CompactPlus3168.checked3178,CompactPlus3168.small3178,CompactPlus3168.nodes3178,NodePlus49.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus3168.p3179,GridPlus.atNode 3179,GridPlus.atNode 3180,NodePlus49.w43,CompactPlus3168.checked3179,CompactPlus3168.small3179,CompactPlus3168.nodes3179,NodePlus49.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus3168.p3180,GridPlus.atNode 3180,GridPlus.atNode 3181,NodePlus49.w44,CompactPlus3168.checked3180,CompactPlus3168.small3180,CompactPlus3168.nodes3180,NodePlus49.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus3168.p3181,GridPlus.atNode 3181,GridPlus.atNode 3182,NodePlus49.w45,CompactPlus3168.checked3181,CompactPlus3168.small3181,CompactPlus3168.nodes3181,NodePlus49.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus3168.p3182,GridPlus.atNode 3182,GridPlus.atNode 3183,NodePlus49.w46,CompactPlus3168.checked3182,CompactPlus3168.small3182,CompactPlus3168.nodes3182,NodePlus49.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus3168.p3183,GridPlus.atNode 3183,GridPlus.atNode 3184,NodePlus49.w47,CompactPlus3168.checked3183,CompactPlus3168.small3183,CompactPlus3168.nodes3183,NodePlus49.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus3184.p3184,GridPlus.atNode 3184,GridPlus.atNode 3185,NodePlus49.w48,CompactPlus3184.checked3184,CompactPlus3184.small3184,CompactPlus3184.nodes3184,NodePlus49.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus3184.p3185,GridPlus.atNode 3185,GridPlus.atNode 3186,NodePlus49.w49,CompactPlus3184.checked3185,CompactPlus3184.small3185,CompactPlus3184.nodes3185,NodePlus49.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus3184.p3186,GridPlus.atNode 3186,GridPlus.atNode 3187,NodePlus49.w50,CompactPlus3184.checked3186,CompactPlus3184.small3186,CompactPlus3184.nodes3186,NodePlus49.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus3184.p3187,GridPlus.atNode 3187,GridPlus.atNode 3188,NodePlus49.w51,CompactPlus3184.checked3187,CompactPlus3184.small3187,CompactPlus3184.nodes3187,NodePlus49.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus3184.p3188,GridPlus.atNode 3188,GridPlus.atNode 3189,NodePlus49.w52,CompactPlus3184.checked3188,CompactPlus3184.small3188,CompactPlus3184.nodes3188,NodePlus49.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus3184.p3189,GridPlus.atNode 3189,GridPlus.atNode 3190,NodePlus49.w53,CompactPlus3184.checked3189,CompactPlus3184.small3189,CompactPlus3184.nodes3189,NodePlus49.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus3184.p3190,GridPlus.atNode 3190,GridPlus.atNode 3191,NodePlus49.w54,CompactPlus3184.checked3190,CompactPlus3184.small3190,CompactPlus3184.nodes3190,NodePlus49.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus3184.p3191,GridPlus.atNode 3191,GridPlus.atNode 3192,NodePlus49.w55,CompactPlus3184.checked3191,CompactPlus3184.small3191,CompactPlus3184.nodes3191,NodePlus49.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus3184.p3192,GridPlus.atNode 3192,GridPlus.atNode 3193,NodePlus49.w56,CompactPlus3184.checked3192,CompactPlus3184.small3192,CompactPlus3184.nodes3192,NodePlus49.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus3184.p3193,GridPlus.atNode 3193,GridPlus.atNode 3194,NodePlus49.w57,CompactPlus3184.checked3193,CompactPlus3184.small3193,CompactPlus3184.nodes3193,NodePlus49.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus3184.p3194,GridPlus.atNode 3194,GridPlus.atNode 3195,NodePlus49.w58,CompactPlus3184.checked3194,CompactPlus3184.small3194,CompactPlus3184.nodes3194,NodePlus49.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus3184.p3195,GridPlus.atNode 3195,GridPlus.atNode 3196,NodePlus49.w59,CompactPlus3184.checked3195,CompactPlus3184.small3195,CompactPlus3184.nodes3195,NodePlus49.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus3184.p3196,GridPlus.atNode 3196,GridPlus.atNode 3197,NodePlus49.w60,CompactPlus3184.checked3196,CompactPlus3184.small3196,CompactPlus3184.nodes3196,NodePlus49.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus3184.p3197,GridPlus.atNode 3197,GridPlus.atNode 3198,NodePlus49.w61,CompactPlus3184.checked3197,CompactPlus3184.small3197,CompactPlus3184.nodes3197,NodePlus49.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus3184.p3198,GridPlus.atNode 3198,GridPlus.atNode 3199,NodePlus49.w62,CompactPlus3184.checked3198,CompactPlus3184.small3198,CompactPlus3184.nodes3198,NodePlus49.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus3184.p3199,GridPlus.atNode 3199,GridPlus.atNode 3200,NodePlus49.w63,CompactPlus3184.checked3199,CompactPlus3184.small3199,CompactPlus3184.nodes3199,NodePlus49.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (3136+j) ∧
    (atRow j).right=GridPlus.atNode (3136+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus49
