import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus3264
import SolitonClassification.Rotating.ResetPackedPlus3280
import SolitonClassification.Rotating.ResetPackedPlus3296
import SolitonClassification.Rotating.ResetPackedPlus3312
namespace SolitonClassification.Rotating.DyadicReset.TilePlus51
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus3264.p3264,GridPlus.atNode 3264,GridPlus.atNode 3265,NodePlus51.w0,CompactPlus3264.checked3264,CompactPlus3264.small3264,CompactPlus3264.nodes3264,NodePlus51.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus3264.p3265,GridPlus.atNode 3265,GridPlus.atNode 3266,NodePlus51.w1,CompactPlus3264.checked3265,CompactPlus3264.small3265,CompactPlus3264.nodes3265,NodePlus51.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus3264.p3266,GridPlus.atNode 3266,GridPlus.atNode 3267,NodePlus51.w2,CompactPlus3264.checked3266,CompactPlus3264.small3266,CompactPlus3264.nodes3266,NodePlus51.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus3264.p3267,GridPlus.atNode 3267,GridPlus.atNode 3268,NodePlus51.w3,CompactPlus3264.checked3267,CompactPlus3264.small3267,CompactPlus3264.nodes3267,NodePlus51.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus3264.p3268,GridPlus.atNode 3268,GridPlus.atNode 3269,NodePlus51.w4,CompactPlus3264.checked3268,CompactPlus3264.small3268,CompactPlus3264.nodes3268,NodePlus51.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus3264.p3269,GridPlus.atNode 3269,GridPlus.atNode 3270,NodePlus51.w5,CompactPlus3264.checked3269,CompactPlus3264.small3269,CompactPlus3264.nodes3269,NodePlus51.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus3264.p3270,GridPlus.atNode 3270,GridPlus.atNode 3271,NodePlus51.w6,CompactPlus3264.checked3270,CompactPlus3264.small3270,CompactPlus3264.nodes3270,NodePlus51.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus3264.p3271,GridPlus.atNode 3271,GridPlus.atNode 3272,NodePlus51.w7,CompactPlus3264.checked3271,CompactPlus3264.small3271,CompactPlus3264.nodes3271,NodePlus51.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus3264.p3272,GridPlus.atNode 3272,GridPlus.atNode 3273,NodePlus51.w8,CompactPlus3264.checked3272,CompactPlus3264.small3272,CompactPlus3264.nodes3272,NodePlus51.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus3264.p3273,GridPlus.atNode 3273,GridPlus.atNode 3274,NodePlus51.w9,CompactPlus3264.checked3273,CompactPlus3264.small3273,CompactPlus3264.nodes3273,NodePlus51.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus3264.p3274,GridPlus.atNode 3274,GridPlus.atNode 3275,NodePlus51.w10,CompactPlus3264.checked3274,CompactPlus3264.small3274,CompactPlus3264.nodes3274,NodePlus51.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus3264.p3275,GridPlus.atNode 3275,GridPlus.atNode 3276,NodePlus51.w11,CompactPlus3264.checked3275,CompactPlus3264.small3275,CompactPlus3264.nodes3275,NodePlus51.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus3264.p3276,GridPlus.atNode 3276,GridPlus.atNode 3277,NodePlus51.w12,CompactPlus3264.checked3276,CompactPlus3264.small3276,CompactPlus3264.nodes3276,NodePlus51.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus3264.p3277,GridPlus.atNode 3277,GridPlus.atNode 3278,NodePlus51.w13,CompactPlus3264.checked3277,CompactPlus3264.small3277,CompactPlus3264.nodes3277,NodePlus51.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus3264.p3278,GridPlus.atNode 3278,GridPlus.atNode 3279,NodePlus51.w14,CompactPlus3264.checked3278,CompactPlus3264.small3278,CompactPlus3264.nodes3278,NodePlus51.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus3264.p3279,GridPlus.atNode 3279,GridPlus.atNode 3280,NodePlus51.w15,CompactPlus3264.checked3279,CompactPlus3264.small3279,CompactPlus3264.nodes3279,NodePlus51.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus3280.p3280,GridPlus.atNode 3280,GridPlus.atNode 3281,NodePlus51.w16,CompactPlus3280.checked3280,CompactPlus3280.small3280,CompactPlus3280.nodes3280,NodePlus51.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus3280.p3281,GridPlus.atNode 3281,GridPlus.atNode 3282,NodePlus51.w17,CompactPlus3280.checked3281,CompactPlus3280.small3281,CompactPlus3280.nodes3281,NodePlus51.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus3280.p3282,GridPlus.atNode 3282,GridPlus.atNode 3283,NodePlus51.w18,CompactPlus3280.checked3282,CompactPlus3280.small3282,CompactPlus3280.nodes3282,NodePlus51.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus3280.p3283,GridPlus.atNode 3283,GridPlus.atNode 3284,NodePlus51.w19,CompactPlus3280.checked3283,CompactPlus3280.small3283,CompactPlus3280.nodes3283,NodePlus51.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus3280.p3284,GridPlus.atNode 3284,GridPlus.atNode 3285,NodePlus51.w20,CompactPlus3280.checked3284,CompactPlus3280.small3284,CompactPlus3280.nodes3284,NodePlus51.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus3280.p3285,GridPlus.atNode 3285,GridPlus.atNode 3286,NodePlus51.w21,CompactPlus3280.checked3285,CompactPlus3280.small3285,CompactPlus3280.nodes3285,NodePlus51.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus3280.p3286,GridPlus.atNode 3286,GridPlus.atNode 3287,NodePlus51.w22,CompactPlus3280.checked3286,CompactPlus3280.small3286,CompactPlus3280.nodes3286,NodePlus51.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus3280.p3287,GridPlus.atNode 3287,GridPlus.atNode 3288,NodePlus51.w23,CompactPlus3280.checked3287,CompactPlus3280.small3287,CompactPlus3280.nodes3287,NodePlus51.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus3280.p3288,GridPlus.atNode 3288,GridPlus.atNode 3289,NodePlus51.w24,CompactPlus3280.checked3288,CompactPlus3280.small3288,CompactPlus3280.nodes3288,NodePlus51.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus3280.p3289,GridPlus.atNode 3289,GridPlus.atNode 3290,NodePlus51.w25,CompactPlus3280.checked3289,CompactPlus3280.small3289,CompactPlus3280.nodes3289,NodePlus51.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus3280.p3290,GridPlus.atNode 3290,GridPlus.atNode 3291,NodePlus51.w26,CompactPlus3280.checked3290,CompactPlus3280.small3290,CompactPlus3280.nodes3290,NodePlus51.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus3280.p3291,GridPlus.atNode 3291,GridPlus.atNode 3292,NodePlus51.w27,CompactPlus3280.checked3291,CompactPlus3280.small3291,CompactPlus3280.nodes3291,NodePlus51.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus3280.p3292,GridPlus.atNode 3292,GridPlus.atNode 3293,NodePlus51.w28,CompactPlus3280.checked3292,CompactPlus3280.small3292,CompactPlus3280.nodes3292,NodePlus51.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus3280.p3293,GridPlus.atNode 3293,GridPlus.atNode 3294,NodePlus51.w29,CompactPlus3280.checked3293,CompactPlus3280.small3293,CompactPlus3280.nodes3293,NodePlus51.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus3280.p3294,GridPlus.atNode 3294,GridPlus.atNode 3295,NodePlus51.w30,CompactPlus3280.checked3294,CompactPlus3280.small3294,CompactPlus3280.nodes3294,NodePlus51.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus3280.p3295,GridPlus.atNode 3295,GridPlus.atNode 3296,NodePlus51.w31,CompactPlus3280.checked3295,CompactPlus3280.small3295,CompactPlus3280.nodes3295,NodePlus51.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus3296.p3296,GridPlus.atNode 3296,GridPlus.atNode 3297,NodePlus51.w32,CompactPlus3296.checked3296,CompactPlus3296.small3296,CompactPlus3296.nodes3296,NodePlus51.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus3296.p3297,GridPlus.atNode 3297,GridPlus.atNode 3298,NodePlus51.w33,CompactPlus3296.checked3297,CompactPlus3296.small3297,CompactPlus3296.nodes3297,NodePlus51.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus3296.p3298,GridPlus.atNode 3298,GridPlus.atNode 3299,NodePlus51.w34,CompactPlus3296.checked3298,CompactPlus3296.small3298,CompactPlus3296.nodes3298,NodePlus51.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus3296.p3299,GridPlus.atNode 3299,GridPlus.atNode 3300,NodePlus51.w35,CompactPlus3296.checked3299,CompactPlus3296.small3299,CompactPlus3296.nodes3299,NodePlus51.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus3296.p3300,GridPlus.atNode 3300,GridPlus.atNode 3301,NodePlus51.w36,CompactPlus3296.checked3300,CompactPlus3296.small3300,CompactPlus3296.nodes3300,NodePlus51.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus3296.p3301,GridPlus.atNode 3301,GridPlus.atNode 3302,NodePlus51.w37,CompactPlus3296.checked3301,CompactPlus3296.small3301,CompactPlus3296.nodes3301,NodePlus51.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus3296.p3302,GridPlus.atNode 3302,GridPlus.atNode 3303,NodePlus51.w38,CompactPlus3296.checked3302,CompactPlus3296.small3302,CompactPlus3296.nodes3302,NodePlus51.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus3296.p3303,GridPlus.atNode 3303,GridPlus.atNode 3304,NodePlus51.w39,CompactPlus3296.checked3303,CompactPlus3296.small3303,CompactPlus3296.nodes3303,NodePlus51.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus3296.p3304,GridPlus.atNode 3304,GridPlus.atNode 3305,NodePlus51.w40,CompactPlus3296.checked3304,CompactPlus3296.small3304,CompactPlus3296.nodes3304,NodePlus51.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus3296.p3305,GridPlus.atNode 3305,GridPlus.atNode 3306,NodePlus51.w41,CompactPlus3296.checked3305,CompactPlus3296.small3305,CompactPlus3296.nodes3305,NodePlus51.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus3296.p3306,GridPlus.atNode 3306,GridPlus.atNode 3307,NodePlus51.w42,CompactPlus3296.checked3306,CompactPlus3296.small3306,CompactPlus3296.nodes3306,NodePlus51.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus3296.p3307,GridPlus.atNode 3307,GridPlus.atNode 3308,NodePlus51.w43,CompactPlus3296.checked3307,CompactPlus3296.small3307,CompactPlus3296.nodes3307,NodePlus51.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus3296.p3308,GridPlus.atNode 3308,GridPlus.atNode 3309,NodePlus51.w44,CompactPlus3296.checked3308,CompactPlus3296.small3308,CompactPlus3296.nodes3308,NodePlus51.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus3296.p3309,GridPlus.atNode 3309,GridPlus.atNode 3310,NodePlus51.w45,CompactPlus3296.checked3309,CompactPlus3296.small3309,CompactPlus3296.nodes3309,NodePlus51.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus3296.p3310,GridPlus.atNode 3310,GridPlus.atNode 3311,NodePlus51.w46,CompactPlus3296.checked3310,CompactPlus3296.small3310,CompactPlus3296.nodes3310,NodePlus51.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus3296.p3311,GridPlus.atNode 3311,GridPlus.atNode 3312,NodePlus51.w47,CompactPlus3296.checked3311,CompactPlus3296.small3311,CompactPlus3296.nodes3311,NodePlus51.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus3312.p3312,GridPlus.atNode 3312,GridPlus.atNode 3313,NodePlus51.w48,CompactPlus3312.checked3312,CompactPlus3312.small3312,CompactPlus3312.nodes3312,NodePlus51.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus3312.p3313,GridPlus.atNode 3313,GridPlus.atNode 3314,NodePlus51.w49,CompactPlus3312.checked3313,CompactPlus3312.small3313,CompactPlus3312.nodes3313,NodePlus51.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus3312.p3314,GridPlus.atNode 3314,GridPlus.atNode 3315,NodePlus51.w50,CompactPlus3312.checked3314,CompactPlus3312.small3314,CompactPlus3312.nodes3314,NodePlus51.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus3312.p3315,GridPlus.atNode 3315,GridPlus.atNode 3316,NodePlus51.w51,CompactPlus3312.checked3315,CompactPlus3312.small3315,CompactPlus3312.nodes3315,NodePlus51.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus3312.p3316,GridPlus.atNode 3316,GridPlus.atNode 3317,NodePlus51.w52,CompactPlus3312.checked3316,CompactPlus3312.small3316,CompactPlus3312.nodes3316,NodePlus51.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus3312.p3317,GridPlus.atNode 3317,GridPlus.atNode 3318,NodePlus51.w53,CompactPlus3312.checked3317,CompactPlus3312.small3317,CompactPlus3312.nodes3317,NodePlus51.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus3312.p3318,GridPlus.atNode 3318,GridPlus.atNode 3319,NodePlus51.w54,CompactPlus3312.checked3318,CompactPlus3312.small3318,CompactPlus3312.nodes3318,NodePlus51.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus3312.p3319,GridPlus.atNode 3319,GridPlus.atNode 3320,NodePlus51.w55,CompactPlus3312.checked3319,CompactPlus3312.small3319,CompactPlus3312.nodes3319,NodePlus51.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus3312.p3320,GridPlus.atNode 3320,GridPlus.atNode 3321,NodePlus51.w56,CompactPlus3312.checked3320,CompactPlus3312.small3320,CompactPlus3312.nodes3320,NodePlus51.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus3312.p3321,GridPlus.atNode 3321,GridPlus.atNode 3322,NodePlus51.w57,CompactPlus3312.checked3321,CompactPlus3312.small3321,CompactPlus3312.nodes3321,NodePlus51.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus3312.p3322,GridPlus.atNode 3322,GridPlus.atNode 3323,NodePlus51.w58,CompactPlus3312.checked3322,CompactPlus3312.small3322,CompactPlus3312.nodes3322,NodePlus51.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus3312.p3323,GridPlus.atNode 3323,GridPlus.atNode 3324,NodePlus51.w59,CompactPlus3312.checked3323,CompactPlus3312.small3323,CompactPlus3312.nodes3323,NodePlus51.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus3312.p3324,GridPlus.atNode 3324,GridPlus.atNode 3325,NodePlus51.w60,CompactPlus3312.checked3324,CompactPlus3312.small3324,CompactPlus3312.nodes3324,NodePlus51.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus3312.p3325,GridPlus.atNode 3325,GridPlus.atNode 3326,NodePlus51.w61,CompactPlus3312.checked3325,CompactPlus3312.small3325,CompactPlus3312.nodes3325,NodePlus51.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus3312.p3326,GridPlus.atNode 3326,GridPlus.atNode 3327,NodePlus51.w62,CompactPlus3312.checked3326,CompactPlus3312.small3326,CompactPlus3312.nodes3326,NodePlus51.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus3312.p3327,GridPlus.atNode 3327,GridPlus.atNode 3328,NodePlus51.w63,CompactPlus3312.checked3327,CompactPlus3312.small3327,CompactPlus3312.nodes3327,NodePlus51.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (3264+j) ∧
    (atRow j).right=GridPlus.atNode (3264+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus51
