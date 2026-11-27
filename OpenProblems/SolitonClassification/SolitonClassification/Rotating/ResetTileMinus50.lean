import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus3200
import SolitonClassification.Rotating.ResetPackedMinus3216
import SolitonClassification.Rotating.ResetPackedMinus3232
import SolitonClassification.Rotating.ResetPackedMinus3248
namespace SolitonClassification.Rotating.DyadicReset.TileMinus50
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3200.p3200,GridMinus.atNode 3200,GridMinus.atNode 3201,NodeMinus50.w0,CompactMinus3200.checked3200,CompactMinus3200.small3200,CompactMinus3200.nodes3200,NodeMinus50.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3200.p3201,GridMinus.atNode 3201,GridMinus.atNode 3202,NodeMinus50.w1,CompactMinus3200.checked3201,CompactMinus3200.small3201,CompactMinus3200.nodes3201,NodeMinus50.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3200.p3202,GridMinus.atNode 3202,GridMinus.atNode 3203,NodeMinus50.w2,CompactMinus3200.checked3202,CompactMinus3200.small3202,CompactMinus3200.nodes3202,NodeMinus50.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3200.p3203,GridMinus.atNode 3203,GridMinus.atNode 3204,NodeMinus50.w3,CompactMinus3200.checked3203,CompactMinus3200.small3203,CompactMinus3200.nodes3203,NodeMinus50.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3200.p3204,GridMinus.atNode 3204,GridMinus.atNode 3205,NodeMinus50.w4,CompactMinus3200.checked3204,CompactMinus3200.small3204,CompactMinus3200.nodes3204,NodeMinus50.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3200.p3205,GridMinus.atNode 3205,GridMinus.atNode 3206,NodeMinus50.w5,CompactMinus3200.checked3205,CompactMinus3200.small3205,CompactMinus3200.nodes3205,NodeMinus50.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3200.p3206,GridMinus.atNode 3206,GridMinus.atNode 3207,NodeMinus50.w6,CompactMinus3200.checked3206,CompactMinus3200.small3206,CompactMinus3200.nodes3206,NodeMinus50.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3200.p3207,GridMinus.atNode 3207,GridMinus.atNode 3208,NodeMinus50.w7,CompactMinus3200.checked3207,CompactMinus3200.small3207,CompactMinus3200.nodes3207,NodeMinus50.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3200.p3208,GridMinus.atNode 3208,GridMinus.atNode 3209,NodeMinus50.w8,CompactMinus3200.checked3208,CompactMinus3200.small3208,CompactMinus3200.nodes3208,NodeMinus50.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3200.p3209,GridMinus.atNode 3209,GridMinus.atNode 3210,NodeMinus50.w9,CompactMinus3200.checked3209,CompactMinus3200.small3209,CompactMinus3200.nodes3209,NodeMinus50.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3200.p3210,GridMinus.atNode 3210,GridMinus.atNode 3211,NodeMinus50.w10,CompactMinus3200.checked3210,CompactMinus3200.small3210,CompactMinus3200.nodes3210,NodeMinus50.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3200.p3211,GridMinus.atNode 3211,GridMinus.atNode 3212,NodeMinus50.w11,CompactMinus3200.checked3211,CompactMinus3200.small3211,CompactMinus3200.nodes3211,NodeMinus50.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3200.p3212,GridMinus.atNode 3212,GridMinus.atNode 3213,NodeMinus50.w12,CompactMinus3200.checked3212,CompactMinus3200.small3212,CompactMinus3200.nodes3212,NodeMinus50.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3200.p3213,GridMinus.atNode 3213,GridMinus.atNode 3214,NodeMinus50.w13,CompactMinus3200.checked3213,CompactMinus3200.small3213,CompactMinus3200.nodes3213,NodeMinus50.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3200.p3214,GridMinus.atNode 3214,GridMinus.atNode 3215,NodeMinus50.w14,CompactMinus3200.checked3214,CompactMinus3200.small3214,CompactMinus3200.nodes3214,NodeMinus50.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3200.p3215,GridMinus.atNode 3215,GridMinus.atNode 3216,NodeMinus50.w15,CompactMinus3200.checked3215,CompactMinus3200.small3215,CompactMinus3200.nodes3215,NodeMinus50.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3216.p3216,GridMinus.atNode 3216,GridMinus.atNode 3217,NodeMinus50.w16,CompactMinus3216.checked3216,CompactMinus3216.small3216,CompactMinus3216.nodes3216,NodeMinus50.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3216.p3217,GridMinus.atNode 3217,GridMinus.atNode 3218,NodeMinus50.w17,CompactMinus3216.checked3217,CompactMinus3216.small3217,CompactMinus3216.nodes3217,NodeMinus50.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3216.p3218,GridMinus.atNode 3218,GridMinus.atNode 3219,NodeMinus50.w18,CompactMinus3216.checked3218,CompactMinus3216.small3218,CompactMinus3216.nodes3218,NodeMinus50.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3216.p3219,GridMinus.atNode 3219,GridMinus.atNode 3220,NodeMinus50.w19,CompactMinus3216.checked3219,CompactMinus3216.small3219,CompactMinus3216.nodes3219,NodeMinus50.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3216.p3220,GridMinus.atNode 3220,GridMinus.atNode 3221,NodeMinus50.w20,CompactMinus3216.checked3220,CompactMinus3216.small3220,CompactMinus3216.nodes3220,NodeMinus50.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3216.p3221,GridMinus.atNode 3221,GridMinus.atNode 3222,NodeMinus50.w21,CompactMinus3216.checked3221,CompactMinus3216.small3221,CompactMinus3216.nodes3221,NodeMinus50.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3216.p3222,GridMinus.atNode 3222,GridMinus.atNode 3223,NodeMinus50.w22,CompactMinus3216.checked3222,CompactMinus3216.small3222,CompactMinus3216.nodes3222,NodeMinus50.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3216.p3223,GridMinus.atNode 3223,GridMinus.atNode 3224,NodeMinus50.w23,CompactMinus3216.checked3223,CompactMinus3216.small3223,CompactMinus3216.nodes3223,NodeMinus50.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3216.p3224,GridMinus.atNode 3224,GridMinus.atNode 3225,NodeMinus50.w24,CompactMinus3216.checked3224,CompactMinus3216.small3224,CompactMinus3216.nodes3224,NodeMinus50.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3216.p3225,GridMinus.atNode 3225,GridMinus.atNode 3226,NodeMinus50.w25,CompactMinus3216.checked3225,CompactMinus3216.small3225,CompactMinus3216.nodes3225,NodeMinus50.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3216.p3226,GridMinus.atNode 3226,GridMinus.atNode 3227,NodeMinus50.w26,CompactMinus3216.checked3226,CompactMinus3216.small3226,CompactMinus3216.nodes3226,NodeMinus50.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3216.p3227,GridMinus.atNode 3227,GridMinus.atNode 3228,NodeMinus50.w27,CompactMinus3216.checked3227,CompactMinus3216.small3227,CompactMinus3216.nodes3227,NodeMinus50.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3216.p3228,GridMinus.atNode 3228,GridMinus.atNode 3229,NodeMinus50.w28,CompactMinus3216.checked3228,CompactMinus3216.small3228,CompactMinus3216.nodes3228,NodeMinus50.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3216.p3229,GridMinus.atNode 3229,GridMinus.atNode 3230,NodeMinus50.w29,CompactMinus3216.checked3229,CompactMinus3216.small3229,CompactMinus3216.nodes3229,NodeMinus50.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3216.p3230,GridMinus.atNode 3230,GridMinus.atNode 3231,NodeMinus50.w30,CompactMinus3216.checked3230,CompactMinus3216.small3230,CompactMinus3216.nodes3230,NodeMinus50.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3216.p3231,GridMinus.atNode 3231,GridMinus.atNode 3232,NodeMinus50.w31,CompactMinus3216.checked3231,CompactMinus3216.small3231,CompactMinus3216.nodes3231,NodeMinus50.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3232.p3232,GridMinus.atNode 3232,GridMinus.atNode 3233,NodeMinus50.w32,CompactMinus3232.checked3232,CompactMinus3232.small3232,CompactMinus3232.nodes3232,NodeMinus50.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3232.p3233,GridMinus.atNode 3233,GridMinus.atNode 3234,NodeMinus50.w33,CompactMinus3232.checked3233,CompactMinus3232.small3233,CompactMinus3232.nodes3233,NodeMinus50.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3232.p3234,GridMinus.atNode 3234,GridMinus.atNode 3235,NodeMinus50.w34,CompactMinus3232.checked3234,CompactMinus3232.small3234,CompactMinus3232.nodes3234,NodeMinus50.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3232.p3235,GridMinus.atNode 3235,GridMinus.atNode 3236,NodeMinus50.w35,CompactMinus3232.checked3235,CompactMinus3232.small3235,CompactMinus3232.nodes3235,NodeMinus50.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3232.p3236,GridMinus.atNode 3236,GridMinus.atNode 3237,NodeMinus50.w36,CompactMinus3232.checked3236,CompactMinus3232.small3236,CompactMinus3232.nodes3236,NodeMinus50.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3232.p3237,GridMinus.atNode 3237,GridMinus.atNode 3238,NodeMinus50.w37,CompactMinus3232.checked3237,CompactMinus3232.small3237,CompactMinus3232.nodes3237,NodeMinus50.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3232.p3238,GridMinus.atNode 3238,GridMinus.atNode 3239,NodeMinus50.w38,CompactMinus3232.checked3238,CompactMinus3232.small3238,CompactMinus3232.nodes3238,NodeMinus50.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3232.p3239,GridMinus.atNode 3239,GridMinus.atNode 3240,NodeMinus50.w39,CompactMinus3232.checked3239,CompactMinus3232.small3239,CompactMinus3232.nodes3239,NodeMinus50.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3232.p3240,GridMinus.atNode 3240,GridMinus.atNode 3241,NodeMinus50.w40,CompactMinus3232.checked3240,CompactMinus3232.small3240,CompactMinus3232.nodes3240,NodeMinus50.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3232.p3241,GridMinus.atNode 3241,GridMinus.atNode 3242,NodeMinus50.w41,CompactMinus3232.checked3241,CompactMinus3232.small3241,CompactMinus3232.nodes3241,NodeMinus50.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3232.p3242,GridMinus.atNode 3242,GridMinus.atNode 3243,NodeMinus50.w42,CompactMinus3232.checked3242,CompactMinus3232.small3242,CompactMinus3232.nodes3242,NodeMinus50.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3232.p3243,GridMinus.atNode 3243,GridMinus.atNode 3244,NodeMinus50.w43,CompactMinus3232.checked3243,CompactMinus3232.small3243,CompactMinus3232.nodes3243,NodeMinus50.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3232.p3244,GridMinus.atNode 3244,GridMinus.atNode 3245,NodeMinus50.w44,CompactMinus3232.checked3244,CompactMinus3232.small3244,CompactMinus3232.nodes3244,NodeMinus50.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3232.p3245,GridMinus.atNode 3245,GridMinus.atNode 3246,NodeMinus50.w45,CompactMinus3232.checked3245,CompactMinus3232.small3245,CompactMinus3232.nodes3245,NodeMinus50.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3232.p3246,GridMinus.atNode 3246,GridMinus.atNode 3247,NodeMinus50.w46,CompactMinus3232.checked3246,CompactMinus3232.small3246,CompactMinus3232.nodes3246,NodeMinus50.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3232.p3247,GridMinus.atNode 3247,GridMinus.atNode 3248,NodeMinus50.w47,CompactMinus3232.checked3247,CompactMinus3232.small3247,CompactMinus3232.nodes3247,NodeMinus50.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3248.p3248,GridMinus.atNode 3248,GridMinus.atNode 3249,NodeMinus50.w48,CompactMinus3248.checked3248,CompactMinus3248.small3248,CompactMinus3248.nodes3248,NodeMinus50.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3248.p3249,GridMinus.atNode 3249,GridMinus.atNode 3250,NodeMinus50.w49,CompactMinus3248.checked3249,CompactMinus3248.small3249,CompactMinus3248.nodes3249,NodeMinus50.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3248.p3250,GridMinus.atNode 3250,GridMinus.atNode 3251,NodeMinus50.w50,CompactMinus3248.checked3250,CompactMinus3248.small3250,CompactMinus3248.nodes3250,NodeMinus50.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3248.p3251,GridMinus.atNode 3251,GridMinus.atNode 3252,NodeMinus50.w51,CompactMinus3248.checked3251,CompactMinus3248.small3251,CompactMinus3248.nodes3251,NodeMinus50.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3248.p3252,GridMinus.atNode 3252,GridMinus.atNode 3253,NodeMinus50.w52,CompactMinus3248.checked3252,CompactMinus3248.small3252,CompactMinus3248.nodes3252,NodeMinus50.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3248.p3253,GridMinus.atNode 3253,GridMinus.atNode 3254,NodeMinus50.w53,CompactMinus3248.checked3253,CompactMinus3248.small3253,CompactMinus3248.nodes3253,NodeMinus50.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3248.p3254,GridMinus.atNode 3254,GridMinus.atNode 3255,NodeMinus50.w54,CompactMinus3248.checked3254,CompactMinus3248.small3254,CompactMinus3248.nodes3254,NodeMinus50.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3248.p3255,GridMinus.atNode 3255,GridMinus.atNode 3256,NodeMinus50.w55,CompactMinus3248.checked3255,CompactMinus3248.small3255,CompactMinus3248.nodes3255,NodeMinus50.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3248.p3256,GridMinus.atNode 3256,GridMinus.atNode 3257,NodeMinus50.w56,CompactMinus3248.checked3256,CompactMinus3248.small3256,CompactMinus3248.nodes3256,NodeMinus50.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3248.p3257,GridMinus.atNode 3257,GridMinus.atNode 3258,NodeMinus50.w57,CompactMinus3248.checked3257,CompactMinus3248.small3257,CompactMinus3248.nodes3257,NodeMinus50.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3248.p3258,GridMinus.atNode 3258,GridMinus.atNode 3259,NodeMinus50.w58,CompactMinus3248.checked3258,CompactMinus3248.small3258,CompactMinus3248.nodes3258,NodeMinus50.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3248.p3259,GridMinus.atNode 3259,GridMinus.atNode 3260,NodeMinus50.w59,CompactMinus3248.checked3259,CompactMinus3248.small3259,CompactMinus3248.nodes3259,NodeMinus50.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3248.p3260,GridMinus.atNode 3260,GridMinus.atNode 3261,NodeMinus50.w60,CompactMinus3248.checked3260,CompactMinus3248.small3260,CompactMinus3248.nodes3260,NodeMinus50.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3248.p3261,GridMinus.atNode 3261,GridMinus.atNode 3262,NodeMinus50.w61,CompactMinus3248.checked3261,CompactMinus3248.small3261,CompactMinus3248.nodes3261,NodeMinus50.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3248.p3262,GridMinus.atNode 3262,GridMinus.atNode 3263,NodeMinus50.w62,CompactMinus3248.checked3262,CompactMinus3248.small3262,CompactMinus3248.nodes3262,NodeMinus50.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3248.p3263,GridMinus.atNode 3263,GridMinus.atNode 3264,NodeMinus50.w63,CompactMinus3248.checked3263,CompactMinus3248.small3263,CompactMinus3248.nodes3263,NodeMinus50.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (3200+j) ∧
    (atRow j).right=GridMinus.atNode (3200+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus50
