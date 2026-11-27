import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus3200
import SolitonClassification.Rotating.ResetPackedPlus3216
import SolitonClassification.Rotating.ResetPackedPlus3232
import SolitonClassification.Rotating.ResetPackedPlus3248
namespace SolitonClassification.Rotating.DyadicReset.TilePlus50
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus3200.p3200,GridPlus.atNode 3200,GridPlus.atNode 3201,NodePlus50.w0,CompactPlus3200.checked3200,CompactPlus3200.small3200,CompactPlus3200.nodes3200,NodePlus50.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus3200.p3201,GridPlus.atNode 3201,GridPlus.atNode 3202,NodePlus50.w1,CompactPlus3200.checked3201,CompactPlus3200.small3201,CompactPlus3200.nodes3201,NodePlus50.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus3200.p3202,GridPlus.atNode 3202,GridPlus.atNode 3203,NodePlus50.w2,CompactPlus3200.checked3202,CompactPlus3200.small3202,CompactPlus3200.nodes3202,NodePlus50.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus3200.p3203,GridPlus.atNode 3203,GridPlus.atNode 3204,NodePlus50.w3,CompactPlus3200.checked3203,CompactPlus3200.small3203,CompactPlus3200.nodes3203,NodePlus50.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus3200.p3204,GridPlus.atNode 3204,GridPlus.atNode 3205,NodePlus50.w4,CompactPlus3200.checked3204,CompactPlus3200.small3204,CompactPlus3200.nodes3204,NodePlus50.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus3200.p3205,GridPlus.atNode 3205,GridPlus.atNode 3206,NodePlus50.w5,CompactPlus3200.checked3205,CompactPlus3200.small3205,CompactPlus3200.nodes3205,NodePlus50.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus3200.p3206,GridPlus.atNode 3206,GridPlus.atNode 3207,NodePlus50.w6,CompactPlus3200.checked3206,CompactPlus3200.small3206,CompactPlus3200.nodes3206,NodePlus50.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus3200.p3207,GridPlus.atNode 3207,GridPlus.atNode 3208,NodePlus50.w7,CompactPlus3200.checked3207,CompactPlus3200.small3207,CompactPlus3200.nodes3207,NodePlus50.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus3200.p3208,GridPlus.atNode 3208,GridPlus.atNode 3209,NodePlus50.w8,CompactPlus3200.checked3208,CompactPlus3200.small3208,CompactPlus3200.nodes3208,NodePlus50.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus3200.p3209,GridPlus.atNode 3209,GridPlus.atNode 3210,NodePlus50.w9,CompactPlus3200.checked3209,CompactPlus3200.small3209,CompactPlus3200.nodes3209,NodePlus50.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus3200.p3210,GridPlus.atNode 3210,GridPlus.atNode 3211,NodePlus50.w10,CompactPlus3200.checked3210,CompactPlus3200.small3210,CompactPlus3200.nodes3210,NodePlus50.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus3200.p3211,GridPlus.atNode 3211,GridPlus.atNode 3212,NodePlus50.w11,CompactPlus3200.checked3211,CompactPlus3200.small3211,CompactPlus3200.nodes3211,NodePlus50.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus3200.p3212,GridPlus.atNode 3212,GridPlus.atNode 3213,NodePlus50.w12,CompactPlus3200.checked3212,CompactPlus3200.small3212,CompactPlus3200.nodes3212,NodePlus50.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus3200.p3213,GridPlus.atNode 3213,GridPlus.atNode 3214,NodePlus50.w13,CompactPlus3200.checked3213,CompactPlus3200.small3213,CompactPlus3200.nodes3213,NodePlus50.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus3200.p3214,GridPlus.atNode 3214,GridPlus.atNode 3215,NodePlus50.w14,CompactPlus3200.checked3214,CompactPlus3200.small3214,CompactPlus3200.nodes3214,NodePlus50.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus3200.p3215,GridPlus.atNode 3215,GridPlus.atNode 3216,NodePlus50.w15,CompactPlus3200.checked3215,CompactPlus3200.small3215,CompactPlus3200.nodes3215,NodePlus50.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus3216.p3216,GridPlus.atNode 3216,GridPlus.atNode 3217,NodePlus50.w16,CompactPlus3216.checked3216,CompactPlus3216.small3216,CompactPlus3216.nodes3216,NodePlus50.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus3216.p3217,GridPlus.atNode 3217,GridPlus.atNode 3218,NodePlus50.w17,CompactPlus3216.checked3217,CompactPlus3216.small3217,CompactPlus3216.nodes3217,NodePlus50.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus3216.p3218,GridPlus.atNode 3218,GridPlus.atNode 3219,NodePlus50.w18,CompactPlus3216.checked3218,CompactPlus3216.small3218,CompactPlus3216.nodes3218,NodePlus50.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus3216.p3219,GridPlus.atNode 3219,GridPlus.atNode 3220,NodePlus50.w19,CompactPlus3216.checked3219,CompactPlus3216.small3219,CompactPlus3216.nodes3219,NodePlus50.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus3216.p3220,GridPlus.atNode 3220,GridPlus.atNode 3221,NodePlus50.w20,CompactPlus3216.checked3220,CompactPlus3216.small3220,CompactPlus3216.nodes3220,NodePlus50.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus3216.p3221,GridPlus.atNode 3221,GridPlus.atNode 3222,NodePlus50.w21,CompactPlus3216.checked3221,CompactPlus3216.small3221,CompactPlus3216.nodes3221,NodePlus50.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus3216.p3222,GridPlus.atNode 3222,GridPlus.atNode 3223,NodePlus50.w22,CompactPlus3216.checked3222,CompactPlus3216.small3222,CompactPlus3216.nodes3222,NodePlus50.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus3216.p3223,GridPlus.atNode 3223,GridPlus.atNode 3224,NodePlus50.w23,CompactPlus3216.checked3223,CompactPlus3216.small3223,CompactPlus3216.nodes3223,NodePlus50.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus3216.p3224,GridPlus.atNode 3224,GridPlus.atNode 3225,NodePlus50.w24,CompactPlus3216.checked3224,CompactPlus3216.small3224,CompactPlus3216.nodes3224,NodePlus50.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus3216.p3225,GridPlus.atNode 3225,GridPlus.atNode 3226,NodePlus50.w25,CompactPlus3216.checked3225,CompactPlus3216.small3225,CompactPlus3216.nodes3225,NodePlus50.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus3216.p3226,GridPlus.atNode 3226,GridPlus.atNode 3227,NodePlus50.w26,CompactPlus3216.checked3226,CompactPlus3216.small3226,CompactPlus3216.nodes3226,NodePlus50.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus3216.p3227,GridPlus.atNode 3227,GridPlus.atNode 3228,NodePlus50.w27,CompactPlus3216.checked3227,CompactPlus3216.small3227,CompactPlus3216.nodes3227,NodePlus50.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus3216.p3228,GridPlus.atNode 3228,GridPlus.atNode 3229,NodePlus50.w28,CompactPlus3216.checked3228,CompactPlus3216.small3228,CompactPlus3216.nodes3228,NodePlus50.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus3216.p3229,GridPlus.atNode 3229,GridPlus.atNode 3230,NodePlus50.w29,CompactPlus3216.checked3229,CompactPlus3216.small3229,CompactPlus3216.nodes3229,NodePlus50.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus3216.p3230,GridPlus.atNode 3230,GridPlus.atNode 3231,NodePlus50.w30,CompactPlus3216.checked3230,CompactPlus3216.small3230,CompactPlus3216.nodes3230,NodePlus50.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus3216.p3231,GridPlus.atNode 3231,GridPlus.atNode 3232,NodePlus50.w31,CompactPlus3216.checked3231,CompactPlus3216.small3231,CompactPlus3216.nodes3231,NodePlus50.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus3232.p3232,GridPlus.atNode 3232,GridPlus.atNode 3233,NodePlus50.w32,CompactPlus3232.checked3232,CompactPlus3232.small3232,CompactPlus3232.nodes3232,NodePlus50.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus3232.p3233,GridPlus.atNode 3233,GridPlus.atNode 3234,NodePlus50.w33,CompactPlus3232.checked3233,CompactPlus3232.small3233,CompactPlus3232.nodes3233,NodePlus50.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus3232.p3234,GridPlus.atNode 3234,GridPlus.atNode 3235,NodePlus50.w34,CompactPlus3232.checked3234,CompactPlus3232.small3234,CompactPlus3232.nodes3234,NodePlus50.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus3232.p3235,GridPlus.atNode 3235,GridPlus.atNode 3236,NodePlus50.w35,CompactPlus3232.checked3235,CompactPlus3232.small3235,CompactPlus3232.nodes3235,NodePlus50.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus3232.p3236,GridPlus.atNode 3236,GridPlus.atNode 3237,NodePlus50.w36,CompactPlus3232.checked3236,CompactPlus3232.small3236,CompactPlus3232.nodes3236,NodePlus50.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus3232.p3237,GridPlus.atNode 3237,GridPlus.atNode 3238,NodePlus50.w37,CompactPlus3232.checked3237,CompactPlus3232.small3237,CompactPlus3232.nodes3237,NodePlus50.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus3232.p3238,GridPlus.atNode 3238,GridPlus.atNode 3239,NodePlus50.w38,CompactPlus3232.checked3238,CompactPlus3232.small3238,CompactPlus3232.nodes3238,NodePlus50.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus3232.p3239,GridPlus.atNode 3239,GridPlus.atNode 3240,NodePlus50.w39,CompactPlus3232.checked3239,CompactPlus3232.small3239,CompactPlus3232.nodes3239,NodePlus50.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus3232.p3240,GridPlus.atNode 3240,GridPlus.atNode 3241,NodePlus50.w40,CompactPlus3232.checked3240,CompactPlus3232.small3240,CompactPlus3232.nodes3240,NodePlus50.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus3232.p3241,GridPlus.atNode 3241,GridPlus.atNode 3242,NodePlus50.w41,CompactPlus3232.checked3241,CompactPlus3232.small3241,CompactPlus3232.nodes3241,NodePlus50.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus3232.p3242,GridPlus.atNode 3242,GridPlus.atNode 3243,NodePlus50.w42,CompactPlus3232.checked3242,CompactPlus3232.small3242,CompactPlus3232.nodes3242,NodePlus50.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus3232.p3243,GridPlus.atNode 3243,GridPlus.atNode 3244,NodePlus50.w43,CompactPlus3232.checked3243,CompactPlus3232.small3243,CompactPlus3232.nodes3243,NodePlus50.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus3232.p3244,GridPlus.atNode 3244,GridPlus.atNode 3245,NodePlus50.w44,CompactPlus3232.checked3244,CompactPlus3232.small3244,CompactPlus3232.nodes3244,NodePlus50.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus3232.p3245,GridPlus.atNode 3245,GridPlus.atNode 3246,NodePlus50.w45,CompactPlus3232.checked3245,CompactPlus3232.small3245,CompactPlus3232.nodes3245,NodePlus50.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus3232.p3246,GridPlus.atNode 3246,GridPlus.atNode 3247,NodePlus50.w46,CompactPlus3232.checked3246,CompactPlus3232.small3246,CompactPlus3232.nodes3246,NodePlus50.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus3232.p3247,GridPlus.atNode 3247,GridPlus.atNode 3248,NodePlus50.w47,CompactPlus3232.checked3247,CompactPlus3232.small3247,CompactPlus3232.nodes3247,NodePlus50.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus3248.p3248,GridPlus.atNode 3248,GridPlus.atNode 3249,NodePlus50.w48,CompactPlus3248.checked3248,CompactPlus3248.small3248,CompactPlus3248.nodes3248,NodePlus50.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus3248.p3249,GridPlus.atNode 3249,GridPlus.atNode 3250,NodePlus50.w49,CompactPlus3248.checked3249,CompactPlus3248.small3249,CompactPlus3248.nodes3249,NodePlus50.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus3248.p3250,GridPlus.atNode 3250,GridPlus.atNode 3251,NodePlus50.w50,CompactPlus3248.checked3250,CompactPlus3248.small3250,CompactPlus3248.nodes3250,NodePlus50.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus3248.p3251,GridPlus.atNode 3251,GridPlus.atNode 3252,NodePlus50.w51,CompactPlus3248.checked3251,CompactPlus3248.small3251,CompactPlus3248.nodes3251,NodePlus50.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus3248.p3252,GridPlus.atNode 3252,GridPlus.atNode 3253,NodePlus50.w52,CompactPlus3248.checked3252,CompactPlus3248.small3252,CompactPlus3248.nodes3252,NodePlus50.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus3248.p3253,GridPlus.atNode 3253,GridPlus.atNode 3254,NodePlus50.w53,CompactPlus3248.checked3253,CompactPlus3248.small3253,CompactPlus3248.nodes3253,NodePlus50.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus3248.p3254,GridPlus.atNode 3254,GridPlus.atNode 3255,NodePlus50.w54,CompactPlus3248.checked3254,CompactPlus3248.small3254,CompactPlus3248.nodes3254,NodePlus50.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus3248.p3255,GridPlus.atNode 3255,GridPlus.atNode 3256,NodePlus50.w55,CompactPlus3248.checked3255,CompactPlus3248.small3255,CompactPlus3248.nodes3255,NodePlus50.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus3248.p3256,GridPlus.atNode 3256,GridPlus.atNode 3257,NodePlus50.w56,CompactPlus3248.checked3256,CompactPlus3248.small3256,CompactPlus3248.nodes3256,NodePlus50.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus3248.p3257,GridPlus.atNode 3257,GridPlus.atNode 3258,NodePlus50.w57,CompactPlus3248.checked3257,CompactPlus3248.small3257,CompactPlus3248.nodes3257,NodePlus50.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus3248.p3258,GridPlus.atNode 3258,GridPlus.atNode 3259,NodePlus50.w58,CompactPlus3248.checked3258,CompactPlus3248.small3258,CompactPlus3248.nodes3258,NodePlus50.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus3248.p3259,GridPlus.atNode 3259,GridPlus.atNode 3260,NodePlus50.w59,CompactPlus3248.checked3259,CompactPlus3248.small3259,CompactPlus3248.nodes3259,NodePlus50.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus3248.p3260,GridPlus.atNode 3260,GridPlus.atNode 3261,NodePlus50.w60,CompactPlus3248.checked3260,CompactPlus3248.small3260,CompactPlus3248.nodes3260,NodePlus50.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus3248.p3261,GridPlus.atNode 3261,GridPlus.atNode 3262,NodePlus50.w61,CompactPlus3248.checked3261,CompactPlus3248.small3261,CompactPlus3248.nodes3261,NodePlus50.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus3248.p3262,GridPlus.atNode 3262,GridPlus.atNode 3263,NodePlus50.w62,CompactPlus3248.checked3262,CompactPlus3248.small3262,CompactPlus3248.nodes3262,NodePlus50.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus3248.p3263,GridPlus.atNode 3263,GridPlus.atNode 3264,NodePlus50.w63,CompactPlus3248.checked3263,CompactPlus3248.small3263,CompactPlus3248.nodes3263,NodePlus50.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (3200+j) ∧
    (atRow j).right=GridPlus.atNode (3200+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus50
