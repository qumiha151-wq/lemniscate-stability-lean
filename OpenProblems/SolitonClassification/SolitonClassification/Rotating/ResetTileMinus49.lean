import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus3136
import SolitonClassification.Rotating.ResetPackedMinus3152
import SolitonClassification.Rotating.ResetPackedMinus3168
import SolitonClassification.Rotating.ResetPackedMinus3184
namespace SolitonClassification.Rotating.DyadicReset.TileMinus49
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3136.p3136,GridMinus.atNode 3136,GridMinus.atNode 3137,NodeMinus49.w0,CompactMinus3136.checked3136,CompactMinus3136.small3136,CompactMinus3136.nodes3136,NodeMinus49.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3136.p3137,GridMinus.atNode 3137,GridMinus.atNode 3138,NodeMinus49.w1,CompactMinus3136.checked3137,CompactMinus3136.small3137,CompactMinus3136.nodes3137,NodeMinus49.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3136.p3138,GridMinus.atNode 3138,GridMinus.atNode 3139,NodeMinus49.w2,CompactMinus3136.checked3138,CompactMinus3136.small3138,CompactMinus3136.nodes3138,NodeMinus49.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3136.p3139,GridMinus.atNode 3139,GridMinus.atNode 3140,NodeMinus49.w3,CompactMinus3136.checked3139,CompactMinus3136.small3139,CompactMinus3136.nodes3139,NodeMinus49.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3136.p3140,GridMinus.atNode 3140,GridMinus.atNode 3141,NodeMinus49.w4,CompactMinus3136.checked3140,CompactMinus3136.small3140,CompactMinus3136.nodes3140,NodeMinus49.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3136.p3141,GridMinus.atNode 3141,GridMinus.atNode 3142,NodeMinus49.w5,CompactMinus3136.checked3141,CompactMinus3136.small3141,CompactMinus3136.nodes3141,NodeMinus49.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3136.p3142,GridMinus.atNode 3142,GridMinus.atNode 3143,NodeMinus49.w6,CompactMinus3136.checked3142,CompactMinus3136.small3142,CompactMinus3136.nodes3142,NodeMinus49.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3136.p3143,GridMinus.atNode 3143,GridMinus.atNode 3144,NodeMinus49.w7,CompactMinus3136.checked3143,CompactMinus3136.small3143,CompactMinus3136.nodes3143,NodeMinus49.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3136.p3144,GridMinus.atNode 3144,GridMinus.atNode 3145,NodeMinus49.w8,CompactMinus3136.checked3144,CompactMinus3136.small3144,CompactMinus3136.nodes3144,NodeMinus49.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3136.p3145,GridMinus.atNode 3145,GridMinus.atNode 3146,NodeMinus49.w9,CompactMinus3136.checked3145,CompactMinus3136.small3145,CompactMinus3136.nodes3145,NodeMinus49.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3136.p3146,GridMinus.atNode 3146,GridMinus.atNode 3147,NodeMinus49.w10,CompactMinus3136.checked3146,CompactMinus3136.small3146,CompactMinus3136.nodes3146,NodeMinus49.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3136.p3147,GridMinus.atNode 3147,GridMinus.atNode 3148,NodeMinus49.w11,CompactMinus3136.checked3147,CompactMinus3136.small3147,CompactMinus3136.nodes3147,NodeMinus49.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3136.p3148,GridMinus.atNode 3148,GridMinus.atNode 3149,NodeMinus49.w12,CompactMinus3136.checked3148,CompactMinus3136.small3148,CompactMinus3136.nodes3148,NodeMinus49.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3136.p3149,GridMinus.atNode 3149,GridMinus.atNode 3150,NodeMinus49.w13,CompactMinus3136.checked3149,CompactMinus3136.small3149,CompactMinus3136.nodes3149,NodeMinus49.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3136.p3150,GridMinus.atNode 3150,GridMinus.atNode 3151,NodeMinus49.w14,CompactMinus3136.checked3150,CompactMinus3136.small3150,CompactMinus3136.nodes3150,NodeMinus49.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3136.p3151,GridMinus.atNode 3151,GridMinus.atNode 3152,NodeMinus49.w15,CompactMinus3136.checked3151,CompactMinus3136.small3151,CompactMinus3136.nodes3151,NodeMinus49.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3152.p3152,GridMinus.atNode 3152,GridMinus.atNode 3153,NodeMinus49.w16,CompactMinus3152.checked3152,CompactMinus3152.small3152,CompactMinus3152.nodes3152,NodeMinus49.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3152.p3153,GridMinus.atNode 3153,GridMinus.atNode 3154,NodeMinus49.w17,CompactMinus3152.checked3153,CompactMinus3152.small3153,CompactMinus3152.nodes3153,NodeMinus49.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3152.p3154,GridMinus.atNode 3154,GridMinus.atNode 3155,NodeMinus49.w18,CompactMinus3152.checked3154,CompactMinus3152.small3154,CompactMinus3152.nodes3154,NodeMinus49.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3152.p3155,GridMinus.atNode 3155,GridMinus.atNode 3156,NodeMinus49.w19,CompactMinus3152.checked3155,CompactMinus3152.small3155,CompactMinus3152.nodes3155,NodeMinus49.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3152.p3156,GridMinus.atNode 3156,GridMinus.atNode 3157,NodeMinus49.w20,CompactMinus3152.checked3156,CompactMinus3152.small3156,CompactMinus3152.nodes3156,NodeMinus49.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3152.p3157,GridMinus.atNode 3157,GridMinus.atNode 3158,NodeMinus49.w21,CompactMinus3152.checked3157,CompactMinus3152.small3157,CompactMinus3152.nodes3157,NodeMinus49.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3152.p3158,GridMinus.atNode 3158,GridMinus.atNode 3159,NodeMinus49.w22,CompactMinus3152.checked3158,CompactMinus3152.small3158,CompactMinus3152.nodes3158,NodeMinus49.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3152.p3159,GridMinus.atNode 3159,GridMinus.atNode 3160,NodeMinus49.w23,CompactMinus3152.checked3159,CompactMinus3152.small3159,CompactMinus3152.nodes3159,NodeMinus49.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3152.p3160,GridMinus.atNode 3160,GridMinus.atNode 3161,NodeMinus49.w24,CompactMinus3152.checked3160,CompactMinus3152.small3160,CompactMinus3152.nodes3160,NodeMinus49.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3152.p3161,GridMinus.atNode 3161,GridMinus.atNode 3162,NodeMinus49.w25,CompactMinus3152.checked3161,CompactMinus3152.small3161,CompactMinus3152.nodes3161,NodeMinus49.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3152.p3162,GridMinus.atNode 3162,GridMinus.atNode 3163,NodeMinus49.w26,CompactMinus3152.checked3162,CompactMinus3152.small3162,CompactMinus3152.nodes3162,NodeMinus49.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3152.p3163,GridMinus.atNode 3163,GridMinus.atNode 3164,NodeMinus49.w27,CompactMinus3152.checked3163,CompactMinus3152.small3163,CompactMinus3152.nodes3163,NodeMinus49.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3152.p3164,GridMinus.atNode 3164,GridMinus.atNode 3165,NodeMinus49.w28,CompactMinus3152.checked3164,CompactMinus3152.small3164,CompactMinus3152.nodes3164,NodeMinus49.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3152.p3165,GridMinus.atNode 3165,GridMinus.atNode 3166,NodeMinus49.w29,CompactMinus3152.checked3165,CompactMinus3152.small3165,CompactMinus3152.nodes3165,NodeMinus49.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3152.p3166,GridMinus.atNode 3166,GridMinus.atNode 3167,NodeMinus49.w30,CompactMinus3152.checked3166,CompactMinus3152.small3166,CompactMinus3152.nodes3166,NodeMinus49.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3152.p3167,GridMinus.atNode 3167,GridMinus.atNode 3168,NodeMinus49.w31,CompactMinus3152.checked3167,CompactMinus3152.small3167,CompactMinus3152.nodes3167,NodeMinus49.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3168.p3168,GridMinus.atNode 3168,GridMinus.atNode 3169,NodeMinus49.w32,CompactMinus3168.checked3168,CompactMinus3168.small3168,CompactMinus3168.nodes3168,NodeMinus49.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3168.p3169,GridMinus.atNode 3169,GridMinus.atNode 3170,NodeMinus49.w33,CompactMinus3168.checked3169,CompactMinus3168.small3169,CompactMinus3168.nodes3169,NodeMinus49.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3168.p3170,GridMinus.atNode 3170,GridMinus.atNode 3171,NodeMinus49.w34,CompactMinus3168.checked3170,CompactMinus3168.small3170,CompactMinus3168.nodes3170,NodeMinus49.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3168.p3171,GridMinus.atNode 3171,GridMinus.atNode 3172,NodeMinus49.w35,CompactMinus3168.checked3171,CompactMinus3168.small3171,CompactMinus3168.nodes3171,NodeMinus49.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3168.p3172,GridMinus.atNode 3172,GridMinus.atNode 3173,NodeMinus49.w36,CompactMinus3168.checked3172,CompactMinus3168.small3172,CompactMinus3168.nodes3172,NodeMinus49.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3168.p3173,GridMinus.atNode 3173,GridMinus.atNode 3174,NodeMinus49.w37,CompactMinus3168.checked3173,CompactMinus3168.small3173,CompactMinus3168.nodes3173,NodeMinus49.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3168.p3174,GridMinus.atNode 3174,GridMinus.atNode 3175,NodeMinus49.w38,CompactMinus3168.checked3174,CompactMinus3168.small3174,CompactMinus3168.nodes3174,NodeMinus49.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3168.p3175,GridMinus.atNode 3175,GridMinus.atNode 3176,NodeMinus49.w39,CompactMinus3168.checked3175,CompactMinus3168.small3175,CompactMinus3168.nodes3175,NodeMinus49.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3168.p3176,GridMinus.atNode 3176,GridMinus.atNode 3177,NodeMinus49.w40,CompactMinus3168.checked3176,CompactMinus3168.small3176,CompactMinus3168.nodes3176,NodeMinus49.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3168.p3177,GridMinus.atNode 3177,GridMinus.atNode 3178,NodeMinus49.w41,CompactMinus3168.checked3177,CompactMinus3168.small3177,CompactMinus3168.nodes3177,NodeMinus49.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3168.p3178,GridMinus.atNode 3178,GridMinus.atNode 3179,NodeMinus49.w42,CompactMinus3168.checked3178,CompactMinus3168.small3178,CompactMinus3168.nodes3178,NodeMinus49.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3168.p3179,GridMinus.atNode 3179,GridMinus.atNode 3180,NodeMinus49.w43,CompactMinus3168.checked3179,CompactMinus3168.small3179,CompactMinus3168.nodes3179,NodeMinus49.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3168.p3180,GridMinus.atNode 3180,GridMinus.atNode 3181,NodeMinus49.w44,CompactMinus3168.checked3180,CompactMinus3168.small3180,CompactMinus3168.nodes3180,NodeMinus49.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3168.p3181,GridMinus.atNode 3181,GridMinus.atNode 3182,NodeMinus49.w45,CompactMinus3168.checked3181,CompactMinus3168.small3181,CompactMinus3168.nodes3181,NodeMinus49.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3168.p3182,GridMinus.atNode 3182,GridMinus.atNode 3183,NodeMinus49.w46,CompactMinus3168.checked3182,CompactMinus3168.small3182,CompactMinus3168.nodes3182,NodeMinus49.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3168.p3183,GridMinus.atNode 3183,GridMinus.atNode 3184,NodeMinus49.w47,CompactMinus3168.checked3183,CompactMinus3168.small3183,CompactMinus3168.nodes3183,NodeMinus49.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3184.p3184,GridMinus.atNode 3184,GridMinus.atNode 3185,NodeMinus49.w48,CompactMinus3184.checked3184,CompactMinus3184.small3184,CompactMinus3184.nodes3184,NodeMinus49.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3184.p3185,GridMinus.atNode 3185,GridMinus.atNode 3186,NodeMinus49.w49,CompactMinus3184.checked3185,CompactMinus3184.small3185,CompactMinus3184.nodes3185,NodeMinus49.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3184.p3186,GridMinus.atNode 3186,GridMinus.atNode 3187,NodeMinus49.w50,CompactMinus3184.checked3186,CompactMinus3184.small3186,CompactMinus3184.nodes3186,NodeMinus49.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3184.p3187,GridMinus.atNode 3187,GridMinus.atNode 3188,NodeMinus49.w51,CompactMinus3184.checked3187,CompactMinus3184.small3187,CompactMinus3184.nodes3187,NodeMinus49.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3184.p3188,GridMinus.atNode 3188,GridMinus.atNode 3189,NodeMinus49.w52,CompactMinus3184.checked3188,CompactMinus3184.small3188,CompactMinus3184.nodes3188,NodeMinus49.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3184.p3189,GridMinus.atNode 3189,GridMinus.atNode 3190,NodeMinus49.w53,CompactMinus3184.checked3189,CompactMinus3184.small3189,CompactMinus3184.nodes3189,NodeMinus49.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3184.p3190,GridMinus.atNode 3190,GridMinus.atNode 3191,NodeMinus49.w54,CompactMinus3184.checked3190,CompactMinus3184.small3190,CompactMinus3184.nodes3190,NodeMinus49.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3184.p3191,GridMinus.atNode 3191,GridMinus.atNode 3192,NodeMinus49.w55,CompactMinus3184.checked3191,CompactMinus3184.small3191,CompactMinus3184.nodes3191,NodeMinus49.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3184.p3192,GridMinus.atNode 3192,GridMinus.atNode 3193,NodeMinus49.w56,CompactMinus3184.checked3192,CompactMinus3184.small3192,CompactMinus3184.nodes3192,NodeMinus49.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3184.p3193,GridMinus.atNode 3193,GridMinus.atNode 3194,NodeMinus49.w57,CompactMinus3184.checked3193,CompactMinus3184.small3193,CompactMinus3184.nodes3193,NodeMinus49.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3184.p3194,GridMinus.atNode 3194,GridMinus.atNode 3195,NodeMinus49.w58,CompactMinus3184.checked3194,CompactMinus3184.small3194,CompactMinus3184.nodes3194,NodeMinus49.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3184.p3195,GridMinus.atNode 3195,GridMinus.atNode 3196,NodeMinus49.w59,CompactMinus3184.checked3195,CompactMinus3184.small3195,CompactMinus3184.nodes3195,NodeMinus49.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3184.p3196,GridMinus.atNode 3196,GridMinus.atNode 3197,NodeMinus49.w60,CompactMinus3184.checked3196,CompactMinus3184.small3196,CompactMinus3184.nodes3196,NodeMinus49.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3184.p3197,GridMinus.atNode 3197,GridMinus.atNode 3198,NodeMinus49.w61,CompactMinus3184.checked3197,CompactMinus3184.small3197,CompactMinus3184.nodes3197,NodeMinus49.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3184.p3198,GridMinus.atNode 3198,GridMinus.atNode 3199,NodeMinus49.w62,CompactMinus3184.checked3198,CompactMinus3184.small3198,CompactMinus3184.nodes3198,NodeMinus49.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3184.p3199,GridMinus.atNode 3199,GridMinus.atNode 3200,NodeMinus49.w63,CompactMinus3184.checked3199,CompactMinus3184.small3199,CompactMinus3184.nodes3199,NodeMinus49.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (3136+j) ∧
    (atRow j).right=GridMinus.atNode (3136+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus49
