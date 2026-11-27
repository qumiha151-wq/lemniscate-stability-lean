import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus3392
import SolitonClassification.Rotating.ResetPackedPlus3408
import SolitonClassification.Rotating.ResetPackedPlus3424
import SolitonClassification.Rotating.ResetPackedPlus3440
namespace SolitonClassification.Rotating.DyadicReset.TilePlus53
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus3392.p3392,GridPlus.atNode 3392,GridPlus.atNode 3393,NodePlus53.w0,CompactPlus3392.checked3392,CompactPlus3392.small3392,CompactPlus3392.nodes3392,NodePlus53.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus3392.p3393,GridPlus.atNode 3393,GridPlus.atNode 3394,NodePlus53.w1,CompactPlus3392.checked3393,CompactPlus3392.small3393,CompactPlus3392.nodes3393,NodePlus53.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus3392.p3394,GridPlus.atNode 3394,GridPlus.atNode 3395,NodePlus53.w2,CompactPlus3392.checked3394,CompactPlus3392.small3394,CompactPlus3392.nodes3394,NodePlus53.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus3392.p3395,GridPlus.atNode 3395,GridPlus.atNode 3396,NodePlus53.w3,CompactPlus3392.checked3395,CompactPlus3392.small3395,CompactPlus3392.nodes3395,NodePlus53.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus3392.p3396,GridPlus.atNode 3396,GridPlus.atNode 3397,NodePlus53.w4,CompactPlus3392.checked3396,CompactPlus3392.small3396,CompactPlus3392.nodes3396,NodePlus53.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus3392.p3397,GridPlus.atNode 3397,GridPlus.atNode 3398,NodePlus53.w5,CompactPlus3392.checked3397,CompactPlus3392.small3397,CompactPlus3392.nodes3397,NodePlus53.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus3392.p3398,GridPlus.atNode 3398,GridPlus.atNode 3399,NodePlus53.w6,CompactPlus3392.checked3398,CompactPlus3392.small3398,CompactPlus3392.nodes3398,NodePlus53.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus3392.p3399,GridPlus.atNode 3399,GridPlus.atNode 3400,NodePlus53.w7,CompactPlus3392.checked3399,CompactPlus3392.small3399,CompactPlus3392.nodes3399,NodePlus53.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus3392.p3400,GridPlus.atNode 3400,GridPlus.atNode 3401,NodePlus53.w8,CompactPlus3392.checked3400,CompactPlus3392.small3400,CompactPlus3392.nodes3400,NodePlus53.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus3392.p3401,GridPlus.atNode 3401,GridPlus.atNode 3402,NodePlus53.w9,CompactPlus3392.checked3401,CompactPlus3392.small3401,CompactPlus3392.nodes3401,NodePlus53.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus3392.p3402,GridPlus.atNode 3402,GridPlus.atNode 3403,NodePlus53.w10,CompactPlus3392.checked3402,CompactPlus3392.small3402,CompactPlus3392.nodes3402,NodePlus53.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus3392.p3403,GridPlus.atNode 3403,GridPlus.atNode 3404,NodePlus53.w11,CompactPlus3392.checked3403,CompactPlus3392.small3403,CompactPlus3392.nodes3403,NodePlus53.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus3392.p3404,GridPlus.atNode 3404,GridPlus.atNode 3405,NodePlus53.w12,CompactPlus3392.checked3404,CompactPlus3392.small3404,CompactPlus3392.nodes3404,NodePlus53.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus3392.p3405,GridPlus.atNode 3405,GridPlus.atNode 3406,NodePlus53.w13,CompactPlus3392.checked3405,CompactPlus3392.small3405,CompactPlus3392.nodes3405,NodePlus53.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus3392.p3406,GridPlus.atNode 3406,GridPlus.atNode 3407,NodePlus53.w14,CompactPlus3392.checked3406,CompactPlus3392.small3406,CompactPlus3392.nodes3406,NodePlus53.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus3392.p3407,GridPlus.atNode 3407,GridPlus.atNode 3408,NodePlus53.w15,CompactPlus3392.checked3407,CompactPlus3392.small3407,CompactPlus3392.nodes3407,NodePlus53.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus3408.p3408,GridPlus.atNode 3408,GridPlus.atNode 3409,NodePlus53.w16,CompactPlus3408.checked3408,CompactPlus3408.small3408,CompactPlus3408.nodes3408,NodePlus53.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus3408.p3409,GridPlus.atNode 3409,GridPlus.atNode 3410,NodePlus53.w17,CompactPlus3408.checked3409,CompactPlus3408.small3409,CompactPlus3408.nodes3409,NodePlus53.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus3408.p3410,GridPlus.atNode 3410,GridPlus.atNode 3411,NodePlus53.w18,CompactPlus3408.checked3410,CompactPlus3408.small3410,CompactPlus3408.nodes3410,NodePlus53.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus3408.p3411,GridPlus.atNode 3411,GridPlus.atNode 3412,NodePlus53.w19,CompactPlus3408.checked3411,CompactPlus3408.small3411,CompactPlus3408.nodes3411,NodePlus53.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus3408.p3412,GridPlus.atNode 3412,GridPlus.atNode 3413,NodePlus53.w20,CompactPlus3408.checked3412,CompactPlus3408.small3412,CompactPlus3408.nodes3412,NodePlus53.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus3408.p3413,GridPlus.atNode 3413,GridPlus.atNode 3414,NodePlus53.w21,CompactPlus3408.checked3413,CompactPlus3408.small3413,CompactPlus3408.nodes3413,NodePlus53.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus3408.p3414,GridPlus.atNode 3414,GridPlus.atNode 3415,NodePlus53.w22,CompactPlus3408.checked3414,CompactPlus3408.small3414,CompactPlus3408.nodes3414,NodePlus53.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus3408.p3415,GridPlus.atNode 3415,GridPlus.atNode 3416,NodePlus53.w23,CompactPlus3408.checked3415,CompactPlus3408.small3415,CompactPlus3408.nodes3415,NodePlus53.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus3408.p3416,GridPlus.atNode 3416,GridPlus.atNode 3417,NodePlus53.w24,CompactPlus3408.checked3416,CompactPlus3408.small3416,CompactPlus3408.nodes3416,NodePlus53.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus3408.p3417,GridPlus.atNode 3417,GridPlus.atNode 3418,NodePlus53.w25,CompactPlus3408.checked3417,CompactPlus3408.small3417,CompactPlus3408.nodes3417,NodePlus53.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus3408.p3418,GridPlus.atNode 3418,GridPlus.atNode 3419,NodePlus53.w26,CompactPlus3408.checked3418,CompactPlus3408.small3418,CompactPlus3408.nodes3418,NodePlus53.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus3408.p3419,GridPlus.atNode 3419,GridPlus.atNode 3420,NodePlus53.w27,CompactPlus3408.checked3419,CompactPlus3408.small3419,CompactPlus3408.nodes3419,NodePlus53.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus3408.p3420,GridPlus.atNode 3420,GridPlus.atNode 3421,NodePlus53.w28,CompactPlus3408.checked3420,CompactPlus3408.small3420,CompactPlus3408.nodes3420,NodePlus53.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus3408.p3421,GridPlus.atNode 3421,GridPlus.atNode 3422,NodePlus53.w29,CompactPlus3408.checked3421,CompactPlus3408.small3421,CompactPlus3408.nodes3421,NodePlus53.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus3408.p3422,GridPlus.atNode 3422,GridPlus.atNode 3423,NodePlus53.w30,CompactPlus3408.checked3422,CompactPlus3408.small3422,CompactPlus3408.nodes3422,NodePlus53.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus3408.p3423,GridPlus.atNode 3423,GridPlus.atNode 3424,NodePlus53.w31,CompactPlus3408.checked3423,CompactPlus3408.small3423,CompactPlus3408.nodes3423,NodePlus53.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus3424.p3424,GridPlus.atNode 3424,GridPlus.atNode 3425,NodePlus53.w32,CompactPlus3424.checked3424,CompactPlus3424.small3424,CompactPlus3424.nodes3424,NodePlus53.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus3424.p3425,GridPlus.atNode 3425,GridPlus.atNode 3426,NodePlus53.w33,CompactPlus3424.checked3425,CompactPlus3424.small3425,CompactPlus3424.nodes3425,NodePlus53.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus3424.p3426,GridPlus.atNode 3426,GridPlus.atNode 3427,NodePlus53.w34,CompactPlus3424.checked3426,CompactPlus3424.small3426,CompactPlus3424.nodes3426,NodePlus53.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus3424.p3427,GridPlus.atNode 3427,GridPlus.atNode 3428,NodePlus53.w35,CompactPlus3424.checked3427,CompactPlus3424.small3427,CompactPlus3424.nodes3427,NodePlus53.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus3424.p3428,GridPlus.atNode 3428,GridPlus.atNode 3429,NodePlus53.w36,CompactPlus3424.checked3428,CompactPlus3424.small3428,CompactPlus3424.nodes3428,NodePlus53.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus3424.p3429,GridPlus.atNode 3429,GridPlus.atNode 3430,NodePlus53.w37,CompactPlus3424.checked3429,CompactPlus3424.small3429,CompactPlus3424.nodes3429,NodePlus53.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus3424.p3430,GridPlus.atNode 3430,GridPlus.atNode 3431,NodePlus53.w38,CompactPlus3424.checked3430,CompactPlus3424.small3430,CompactPlus3424.nodes3430,NodePlus53.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus3424.p3431,GridPlus.atNode 3431,GridPlus.atNode 3432,NodePlus53.w39,CompactPlus3424.checked3431,CompactPlus3424.small3431,CompactPlus3424.nodes3431,NodePlus53.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus3424.p3432,GridPlus.atNode 3432,GridPlus.atNode 3433,NodePlus53.w40,CompactPlus3424.checked3432,CompactPlus3424.small3432,CompactPlus3424.nodes3432,NodePlus53.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus3424.p3433,GridPlus.atNode 3433,GridPlus.atNode 3434,NodePlus53.w41,CompactPlus3424.checked3433,CompactPlus3424.small3433,CompactPlus3424.nodes3433,NodePlus53.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus3424.p3434,GridPlus.atNode 3434,GridPlus.atNode 3435,NodePlus53.w42,CompactPlus3424.checked3434,CompactPlus3424.small3434,CompactPlus3424.nodes3434,NodePlus53.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus3424.p3435,GridPlus.atNode 3435,GridPlus.atNode 3436,NodePlus53.w43,CompactPlus3424.checked3435,CompactPlus3424.small3435,CompactPlus3424.nodes3435,NodePlus53.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus3424.p3436,GridPlus.atNode 3436,GridPlus.atNode 3437,NodePlus53.w44,CompactPlus3424.checked3436,CompactPlus3424.small3436,CompactPlus3424.nodes3436,NodePlus53.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus3424.p3437,GridPlus.atNode 3437,GridPlus.atNode 3438,NodePlus53.w45,CompactPlus3424.checked3437,CompactPlus3424.small3437,CompactPlus3424.nodes3437,NodePlus53.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus3424.p3438,GridPlus.atNode 3438,GridPlus.atNode 3439,NodePlus53.w46,CompactPlus3424.checked3438,CompactPlus3424.small3438,CompactPlus3424.nodes3438,NodePlus53.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus3424.p3439,GridPlus.atNode 3439,GridPlus.atNode 3440,NodePlus53.w47,CompactPlus3424.checked3439,CompactPlus3424.small3439,CompactPlus3424.nodes3439,NodePlus53.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus3440.p3440,GridPlus.atNode 3440,GridPlus.atNode 3441,NodePlus53.w48,CompactPlus3440.checked3440,CompactPlus3440.small3440,CompactPlus3440.nodes3440,NodePlus53.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus3440.p3441,GridPlus.atNode 3441,GridPlus.atNode 3442,NodePlus53.w49,CompactPlus3440.checked3441,CompactPlus3440.small3441,CompactPlus3440.nodes3441,NodePlus53.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus3440.p3442,GridPlus.atNode 3442,GridPlus.atNode 3443,NodePlus53.w50,CompactPlus3440.checked3442,CompactPlus3440.small3442,CompactPlus3440.nodes3442,NodePlus53.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus3440.p3443,GridPlus.atNode 3443,GridPlus.atNode 3444,NodePlus53.w51,CompactPlus3440.checked3443,CompactPlus3440.small3443,CompactPlus3440.nodes3443,NodePlus53.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus3440.p3444,GridPlus.atNode 3444,GridPlus.atNode 3445,NodePlus53.w52,CompactPlus3440.checked3444,CompactPlus3440.small3444,CompactPlus3440.nodes3444,NodePlus53.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus3440.p3445,GridPlus.atNode 3445,GridPlus.atNode 3446,NodePlus53.w53,CompactPlus3440.checked3445,CompactPlus3440.small3445,CompactPlus3440.nodes3445,NodePlus53.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus3440.p3446,GridPlus.atNode 3446,GridPlus.atNode 3447,NodePlus53.w54,CompactPlus3440.checked3446,CompactPlus3440.small3446,CompactPlus3440.nodes3446,NodePlus53.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus3440.p3447,GridPlus.atNode 3447,GridPlus.atNode 3448,NodePlus53.w55,CompactPlus3440.checked3447,CompactPlus3440.small3447,CompactPlus3440.nodes3447,NodePlus53.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus3440.p3448,GridPlus.atNode 3448,GridPlus.atNode 3449,NodePlus53.w56,CompactPlus3440.checked3448,CompactPlus3440.small3448,CompactPlus3440.nodes3448,NodePlus53.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus3440.p3449,GridPlus.atNode 3449,GridPlus.atNode 3450,NodePlus53.w57,CompactPlus3440.checked3449,CompactPlus3440.small3449,CompactPlus3440.nodes3449,NodePlus53.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus3440.p3450,GridPlus.atNode 3450,GridPlus.atNode 3451,NodePlus53.w58,CompactPlus3440.checked3450,CompactPlus3440.small3450,CompactPlus3440.nodes3450,NodePlus53.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus3440.p3451,GridPlus.atNode 3451,GridPlus.atNode 3452,NodePlus53.w59,CompactPlus3440.checked3451,CompactPlus3440.small3451,CompactPlus3440.nodes3451,NodePlus53.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus3440.p3452,GridPlus.atNode 3452,GridPlus.atNode 3453,NodePlus53.w60,CompactPlus3440.checked3452,CompactPlus3440.small3452,CompactPlus3440.nodes3452,NodePlus53.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus3440.p3453,GridPlus.atNode 3453,GridPlus.atNode 3454,NodePlus53.w61,CompactPlus3440.checked3453,CompactPlus3440.small3453,CompactPlus3440.nodes3453,NodePlus53.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus3440.p3454,GridPlus.atNode 3454,GridPlus.atNode 3455,NodePlus53.w62,CompactPlus3440.checked3454,CompactPlus3440.small3454,CompactPlus3440.nodes3454,NodePlus53.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus3440.p3455,GridPlus.atNode 3455,GridPlus.atNode 3456,NodePlus53.w63,CompactPlus3440.checked3455,CompactPlus3440.small3455,CompactPlus3440.nodes3455,NodePlus53.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (3392+j) ∧
    (atRow j).right=GridPlus.atNode (3392+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus53
