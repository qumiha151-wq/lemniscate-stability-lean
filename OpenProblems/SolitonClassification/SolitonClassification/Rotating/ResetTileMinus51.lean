import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus3264
import SolitonClassification.Rotating.ResetPackedMinus3280
import SolitonClassification.Rotating.ResetPackedMinus3296
import SolitonClassification.Rotating.ResetPackedMinus3312
namespace SolitonClassification.Rotating.DyadicReset.TileMinus51
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3264.p3264,GridMinus.atNode 3264,GridMinus.atNode 3265,NodeMinus51.w0,CompactMinus3264.checked3264,CompactMinus3264.small3264,CompactMinus3264.nodes3264,NodeMinus51.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3264.p3265,GridMinus.atNode 3265,GridMinus.atNode 3266,NodeMinus51.w1,CompactMinus3264.checked3265,CompactMinus3264.small3265,CompactMinus3264.nodes3265,NodeMinus51.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3264.p3266,GridMinus.atNode 3266,GridMinus.atNode 3267,NodeMinus51.w2,CompactMinus3264.checked3266,CompactMinus3264.small3266,CompactMinus3264.nodes3266,NodeMinus51.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3264.p3267,GridMinus.atNode 3267,GridMinus.atNode 3268,NodeMinus51.w3,CompactMinus3264.checked3267,CompactMinus3264.small3267,CompactMinus3264.nodes3267,NodeMinus51.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3264.p3268,GridMinus.atNode 3268,GridMinus.atNode 3269,NodeMinus51.w4,CompactMinus3264.checked3268,CompactMinus3264.small3268,CompactMinus3264.nodes3268,NodeMinus51.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3264.p3269,GridMinus.atNode 3269,GridMinus.atNode 3270,NodeMinus51.w5,CompactMinus3264.checked3269,CompactMinus3264.small3269,CompactMinus3264.nodes3269,NodeMinus51.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3264.p3270,GridMinus.atNode 3270,GridMinus.atNode 3271,NodeMinus51.w6,CompactMinus3264.checked3270,CompactMinus3264.small3270,CompactMinus3264.nodes3270,NodeMinus51.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3264.p3271,GridMinus.atNode 3271,GridMinus.atNode 3272,NodeMinus51.w7,CompactMinus3264.checked3271,CompactMinus3264.small3271,CompactMinus3264.nodes3271,NodeMinus51.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3264.p3272,GridMinus.atNode 3272,GridMinus.atNode 3273,NodeMinus51.w8,CompactMinus3264.checked3272,CompactMinus3264.small3272,CompactMinus3264.nodes3272,NodeMinus51.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3264.p3273,GridMinus.atNode 3273,GridMinus.atNode 3274,NodeMinus51.w9,CompactMinus3264.checked3273,CompactMinus3264.small3273,CompactMinus3264.nodes3273,NodeMinus51.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3264.p3274,GridMinus.atNode 3274,GridMinus.atNode 3275,NodeMinus51.w10,CompactMinus3264.checked3274,CompactMinus3264.small3274,CompactMinus3264.nodes3274,NodeMinus51.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3264.p3275,GridMinus.atNode 3275,GridMinus.atNode 3276,NodeMinus51.w11,CompactMinus3264.checked3275,CompactMinus3264.small3275,CompactMinus3264.nodes3275,NodeMinus51.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3264.p3276,GridMinus.atNode 3276,GridMinus.atNode 3277,NodeMinus51.w12,CompactMinus3264.checked3276,CompactMinus3264.small3276,CompactMinus3264.nodes3276,NodeMinus51.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3264.p3277,GridMinus.atNode 3277,GridMinus.atNode 3278,NodeMinus51.w13,CompactMinus3264.checked3277,CompactMinus3264.small3277,CompactMinus3264.nodes3277,NodeMinus51.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3264.p3278,GridMinus.atNode 3278,GridMinus.atNode 3279,NodeMinus51.w14,CompactMinus3264.checked3278,CompactMinus3264.small3278,CompactMinus3264.nodes3278,NodeMinus51.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3264.p3279,GridMinus.atNode 3279,GridMinus.atNode 3280,NodeMinus51.w15,CompactMinus3264.checked3279,CompactMinus3264.small3279,CompactMinus3264.nodes3279,NodeMinus51.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3280.p3280,GridMinus.atNode 3280,GridMinus.atNode 3281,NodeMinus51.w16,CompactMinus3280.checked3280,CompactMinus3280.small3280,CompactMinus3280.nodes3280,NodeMinus51.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3280.p3281,GridMinus.atNode 3281,GridMinus.atNode 3282,NodeMinus51.w17,CompactMinus3280.checked3281,CompactMinus3280.small3281,CompactMinus3280.nodes3281,NodeMinus51.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3280.p3282,GridMinus.atNode 3282,GridMinus.atNode 3283,NodeMinus51.w18,CompactMinus3280.checked3282,CompactMinus3280.small3282,CompactMinus3280.nodes3282,NodeMinus51.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3280.p3283,GridMinus.atNode 3283,GridMinus.atNode 3284,NodeMinus51.w19,CompactMinus3280.checked3283,CompactMinus3280.small3283,CompactMinus3280.nodes3283,NodeMinus51.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3280.p3284,GridMinus.atNode 3284,GridMinus.atNode 3285,NodeMinus51.w20,CompactMinus3280.checked3284,CompactMinus3280.small3284,CompactMinus3280.nodes3284,NodeMinus51.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3280.p3285,GridMinus.atNode 3285,GridMinus.atNode 3286,NodeMinus51.w21,CompactMinus3280.checked3285,CompactMinus3280.small3285,CompactMinus3280.nodes3285,NodeMinus51.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3280.p3286,GridMinus.atNode 3286,GridMinus.atNode 3287,NodeMinus51.w22,CompactMinus3280.checked3286,CompactMinus3280.small3286,CompactMinus3280.nodes3286,NodeMinus51.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3280.p3287,GridMinus.atNode 3287,GridMinus.atNode 3288,NodeMinus51.w23,CompactMinus3280.checked3287,CompactMinus3280.small3287,CompactMinus3280.nodes3287,NodeMinus51.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3280.p3288,GridMinus.atNode 3288,GridMinus.atNode 3289,NodeMinus51.w24,CompactMinus3280.checked3288,CompactMinus3280.small3288,CompactMinus3280.nodes3288,NodeMinus51.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3280.p3289,GridMinus.atNode 3289,GridMinus.atNode 3290,NodeMinus51.w25,CompactMinus3280.checked3289,CompactMinus3280.small3289,CompactMinus3280.nodes3289,NodeMinus51.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3280.p3290,GridMinus.atNode 3290,GridMinus.atNode 3291,NodeMinus51.w26,CompactMinus3280.checked3290,CompactMinus3280.small3290,CompactMinus3280.nodes3290,NodeMinus51.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3280.p3291,GridMinus.atNode 3291,GridMinus.atNode 3292,NodeMinus51.w27,CompactMinus3280.checked3291,CompactMinus3280.small3291,CompactMinus3280.nodes3291,NodeMinus51.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3280.p3292,GridMinus.atNode 3292,GridMinus.atNode 3293,NodeMinus51.w28,CompactMinus3280.checked3292,CompactMinus3280.small3292,CompactMinus3280.nodes3292,NodeMinus51.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3280.p3293,GridMinus.atNode 3293,GridMinus.atNode 3294,NodeMinus51.w29,CompactMinus3280.checked3293,CompactMinus3280.small3293,CompactMinus3280.nodes3293,NodeMinus51.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3280.p3294,GridMinus.atNode 3294,GridMinus.atNode 3295,NodeMinus51.w30,CompactMinus3280.checked3294,CompactMinus3280.small3294,CompactMinus3280.nodes3294,NodeMinus51.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3280.p3295,GridMinus.atNode 3295,GridMinus.atNode 3296,NodeMinus51.w31,CompactMinus3280.checked3295,CompactMinus3280.small3295,CompactMinus3280.nodes3295,NodeMinus51.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3296.p3296,GridMinus.atNode 3296,GridMinus.atNode 3297,NodeMinus51.w32,CompactMinus3296.checked3296,CompactMinus3296.small3296,CompactMinus3296.nodes3296,NodeMinus51.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3296.p3297,GridMinus.atNode 3297,GridMinus.atNode 3298,NodeMinus51.w33,CompactMinus3296.checked3297,CompactMinus3296.small3297,CompactMinus3296.nodes3297,NodeMinus51.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3296.p3298,GridMinus.atNode 3298,GridMinus.atNode 3299,NodeMinus51.w34,CompactMinus3296.checked3298,CompactMinus3296.small3298,CompactMinus3296.nodes3298,NodeMinus51.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3296.p3299,GridMinus.atNode 3299,GridMinus.atNode 3300,NodeMinus51.w35,CompactMinus3296.checked3299,CompactMinus3296.small3299,CompactMinus3296.nodes3299,NodeMinus51.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3296.p3300,GridMinus.atNode 3300,GridMinus.atNode 3301,NodeMinus51.w36,CompactMinus3296.checked3300,CompactMinus3296.small3300,CompactMinus3296.nodes3300,NodeMinus51.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3296.p3301,GridMinus.atNode 3301,GridMinus.atNode 3302,NodeMinus51.w37,CompactMinus3296.checked3301,CompactMinus3296.small3301,CompactMinus3296.nodes3301,NodeMinus51.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3296.p3302,GridMinus.atNode 3302,GridMinus.atNode 3303,NodeMinus51.w38,CompactMinus3296.checked3302,CompactMinus3296.small3302,CompactMinus3296.nodes3302,NodeMinus51.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3296.p3303,GridMinus.atNode 3303,GridMinus.atNode 3304,NodeMinus51.w39,CompactMinus3296.checked3303,CompactMinus3296.small3303,CompactMinus3296.nodes3303,NodeMinus51.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3296.p3304,GridMinus.atNode 3304,GridMinus.atNode 3305,NodeMinus51.w40,CompactMinus3296.checked3304,CompactMinus3296.small3304,CompactMinus3296.nodes3304,NodeMinus51.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3296.p3305,GridMinus.atNode 3305,GridMinus.atNode 3306,NodeMinus51.w41,CompactMinus3296.checked3305,CompactMinus3296.small3305,CompactMinus3296.nodes3305,NodeMinus51.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3296.p3306,GridMinus.atNode 3306,GridMinus.atNode 3307,NodeMinus51.w42,CompactMinus3296.checked3306,CompactMinus3296.small3306,CompactMinus3296.nodes3306,NodeMinus51.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3296.p3307,GridMinus.atNode 3307,GridMinus.atNode 3308,NodeMinus51.w43,CompactMinus3296.checked3307,CompactMinus3296.small3307,CompactMinus3296.nodes3307,NodeMinus51.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3296.p3308,GridMinus.atNode 3308,GridMinus.atNode 3309,NodeMinus51.w44,CompactMinus3296.checked3308,CompactMinus3296.small3308,CompactMinus3296.nodes3308,NodeMinus51.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3296.p3309,GridMinus.atNode 3309,GridMinus.atNode 3310,NodeMinus51.w45,CompactMinus3296.checked3309,CompactMinus3296.small3309,CompactMinus3296.nodes3309,NodeMinus51.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3296.p3310,GridMinus.atNode 3310,GridMinus.atNode 3311,NodeMinus51.w46,CompactMinus3296.checked3310,CompactMinus3296.small3310,CompactMinus3296.nodes3310,NodeMinus51.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3296.p3311,GridMinus.atNode 3311,GridMinus.atNode 3312,NodeMinus51.w47,CompactMinus3296.checked3311,CompactMinus3296.small3311,CompactMinus3296.nodes3311,NodeMinus51.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3312.p3312,GridMinus.atNode 3312,GridMinus.atNode 3313,NodeMinus51.w48,CompactMinus3312.checked3312,CompactMinus3312.small3312,CompactMinus3312.nodes3312,NodeMinus51.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3312.p3313,GridMinus.atNode 3313,GridMinus.atNode 3314,NodeMinus51.w49,CompactMinus3312.checked3313,CompactMinus3312.small3313,CompactMinus3312.nodes3313,NodeMinus51.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3312.p3314,GridMinus.atNode 3314,GridMinus.atNode 3315,NodeMinus51.w50,CompactMinus3312.checked3314,CompactMinus3312.small3314,CompactMinus3312.nodes3314,NodeMinus51.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3312.p3315,GridMinus.atNode 3315,GridMinus.atNode 3316,NodeMinus51.w51,CompactMinus3312.checked3315,CompactMinus3312.small3315,CompactMinus3312.nodes3315,NodeMinus51.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3312.p3316,GridMinus.atNode 3316,GridMinus.atNode 3317,NodeMinus51.w52,CompactMinus3312.checked3316,CompactMinus3312.small3316,CompactMinus3312.nodes3316,NodeMinus51.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3312.p3317,GridMinus.atNode 3317,GridMinus.atNode 3318,NodeMinus51.w53,CompactMinus3312.checked3317,CompactMinus3312.small3317,CompactMinus3312.nodes3317,NodeMinus51.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3312.p3318,GridMinus.atNode 3318,GridMinus.atNode 3319,NodeMinus51.w54,CompactMinus3312.checked3318,CompactMinus3312.small3318,CompactMinus3312.nodes3318,NodeMinus51.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3312.p3319,GridMinus.atNode 3319,GridMinus.atNode 3320,NodeMinus51.w55,CompactMinus3312.checked3319,CompactMinus3312.small3319,CompactMinus3312.nodes3319,NodeMinus51.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3312.p3320,GridMinus.atNode 3320,GridMinus.atNode 3321,NodeMinus51.w56,CompactMinus3312.checked3320,CompactMinus3312.small3320,CompactMinus3312.nodes3320,NodeMinus51.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3312.p3321,GridMinus.atNode 3321,GridMinus.atNode 3322,NodeMinus51.w57,CompactMinus3312.checked3321,CompactMinus3312.small3321,CompactMinus3312.nodes3321,NodeMinus51.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3312.p3322,GridMinus.atNode 3322,GridMinus.atNode 3323,NodeMinus51.w58,CompactMinus3312.checked3322,CompactMinus3312.small3322,CompactMinus3312.nodes3322,NodeMinus51.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3312.p3323,GridMinus.atNode 3323,GridMinus.atNode 3324,NodeMinus51.w59,CompactMinus3312.checked3323,CompactMinus3312.small3323,CompactMinus3312.nodes3323,NodeMinus51.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3312.p3324,GridMinus.atNode 3324,GridMinus.atNode 3325,NodeMinus51.w60,CompactMinus3312.checked3324,CompactMinus3312.small3324,CompactMinus3312.nodes3324,NodeMinus51.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3312.p3325,GridMinus.atNode 3325,GridMinus.atNode 3326,NodeMinus51.w61,CompactMinus3312.checked3325,CompactMinus3312.small3325,CompactMinus3312.nodes3325,NodeMinus51.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3312.p3326,GridMinus.atNode 3326,GridMinus.atNode 3327,NodeMinus51.w62,CompactMinus3312.checked3326,CompactMinus3312.small3326,CompactMinus3312.nodes3326,NodeMinus51.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3312.p3327,GridMinus.atNode 3327,GridMinus.atNode 3328,NodeMinus51.w63,CompactMinus3312.checked3327,CompactMinus3312.small3327,CompactMinus3312.nodes3327,NodeMinus51.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (3264+j) ∧
    (atRow j).right=GridMinus.atNode (3264+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus51
