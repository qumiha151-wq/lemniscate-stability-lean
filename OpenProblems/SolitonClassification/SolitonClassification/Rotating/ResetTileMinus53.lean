import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus3392
import SolitonClassification.Rotating.ResetPackedMinus3408
import SolitonClassification.Rotating.ResetPackedMinus3424
import SolitonClassification.Rotating.ResetPackedMinus3440
namespace SolitonClassification.Rotating.DyadicReset.TileMinus53
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3392.p3392,GridMinus.atNode 3392,GridMinus.atNode 3393,NodeMinus53.w0,CompactMinus3392.checked3392,CompactMinus3392.small3392,CompactMinus3392.nodes3392,NodeMinus53.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3392.p3393,GridMinus.atNode 3393,GridMinus.atNode 3394,NodeMinus53.w1,CompactMinus3392.checked3393,CompactMinus3392.small3393,CompactMinus3392.nodes3393,NodeMinus53.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3392.p3394,GridMinus.atNode 3394,GridMinus.atNode 3395,NodeMinus53.w2,CompactMinus3392.checked3394,CompactMinus3392.small3394,CompactMinus3392.nodes3394,NodeMinus53.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3392.p3395,GridMinus.atNode 3395,GridMinus.atNode 3396,NodeMinus53.w3,CompactMinus3392.checked3395,CompactMinus3392.small3395,CompactMinus3392.nodes3395,NodeMinus53.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3392.p3396,GridMinus.atNode 3396,GridMinus.atNode 3397,NodeMinus53.w4,CompactMinus3392.checked3396,CompactMinus3392.small3396,CompactMinus3392.nodes3396,NodeMinus53.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3392.p3397,GridMinus.atNode 3397,GridMinus.atNode 3398,NodeMinus53.w5,CompactMinus3392.checked3397,CompactMinus3392.small3397,CompactMinus3392.nodes3397,NodeMinus53.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3392.p3398,GridMinus.atNode 3398,GridMinus.atNode 3399,NodeMinus53.w6,CompactMinus3392.checked3398,CompactMinus3392.small3398,CompactMinus3392.nodes3398,NodeMinus53.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3392.p3399,GridMinus.atNode 3399,GridMinus.atNode 3400,NodeMinus53.w7,CompactMinus3392.checked3399,CompactMinus3392.small3399,CompactMinus3392.nodes3399,NodeMinus53.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3392.p3400,GridMinus.atNode 3400,GridMinus.atNode 3401,NodeMinus53.w8,CompactMinus3392.checked3400,CompactMinus3392.small3400,CompactMinus3392.nodes3400,NodeMinus53.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3392.p3401,GridMinus.atNode 3401,GridMinus.atNode 3402,NodeMinus53.w9,CompactMinus3392.checked3401,CompactMinus3392.small3401,CompactMinus3392.nodes3401,NodeMinus53.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3392.p3402,GridMinus.atNode 3402,GridMinus.atNode 3403,NodeMinus53.w10,CompactMinus3392.checked3402,CompactMinus3392.small3402,CompactMinus3392.nodes3402,NodeMinus53.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3392.p3403,GridMinus.atNode 3403,GridMinus.atNode 3404,NodeMinus53.w11,CompactMinus3392.checked3403,CompactMinus3392.small3403,CompactMinus3392.nodes3403,NodeMinus53.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3392.p3404,GridMinus.atNode 3404,GridMinus.atNode 3405,NodeMinus53.w12,CompactMinus3392.checked3404,CompactMinus3392.small3404,CompactMinus3392.nodes3404,NodeMinus53.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3392.p3405,GridMinus.atNode 3405,GridMinus.atNode 3406,NodeMinus53.w13,CompactMinus3392.checked3405,CompactMinus3392.small3405,CompactMinus3392.nodes3405,NodeMinus53.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3392.p3406,GridMinus.atNode 3406,GridMinus.atNode 3407,NodeMinus53.w14,CompactMinus3392.checked3406,CompactMinus3392.small3406,CompactMinus3392.nodes3406,NodeMinus53.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3392.p3407,GridMinus.atNode 3407,GridMinus.atNode 3408,NodeMinus53.w15,CompactMinus3392.checked3407,CompactMinus3392.small3407,CompactMinus3392.nodes3407,NodeMinus53.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3408.p3408,GridMinus.atNode 3408,GridMinus.atNode 3409,NodeMinus53.w16,CompactMinus3408.checked3408,CompactMinus3408.small3408,CompactMinus3408.nodes3408,NodeMinus53.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3408.p3409,GridMinus.atNode 3409,GridMinus.atNode 3410,NodeMinus53.w17,CompactMinus3408.checked3409,CompactMinus3408.small3409,CompactMinus3408.nodes3409,NodeMinus53.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3408.p3410,GridMinus.atNode 3410,GridMinus.atNode 3411,NodeMinus53.w18,CompactMinus3408.checked3410,CompactMinus3408.small3410,CompactMinus3408.nodes3410,NodeMinus53.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3408.p3411,GridMinus.atNode 3411,GridMinus.atNode 3412,NodeMinus53.w19,CompactMinus3408.checked3411,CompactMinus3408.small3411,CompactMinus3408.nodes3411,NodeMinus53.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3408.p3412,GridMinus.atNode 3412,GridMinus.atNode 3413,NodeMinus53.w20,CompactMinus3408.checked3412,CompactMinus3408.small3412,CompactMinus3408.nodes3412,NodeMinus53.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3408.p3413,GridMinus.atNode 3413,GridMinus.atNode 3414,NodeMinus53.w21,CompactMinus3408.checked3413,CompactMinus3408.small3413,CompactMinus3408.nodes3413,NodeMinus53.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3408.p3414,GridMinus.atNode 3414,GridMinus.atNode 3415,NodeMinus53.w22,CompactMinus3408.checked3414,CompactMinus3408.small3414,CompactMinus3408.nodes3414,NodeMinus53.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3408.p3415,GridMinus.atNode 3415,GridMinus.atNode 3416,NodeMinus53.w23,CompactMinus3408.checked3415,CompactMinus3408.small3415,CompactMinus3408.nodes3415,NodeMinus53.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3408.p3416,GridMinus.atNode 3416,GridMinus.atNode 3417,NodeMinus53.w24,CompactMinus3408.checked3416,CompactMinus3408.small3416,CompactMinus3408.nodes3416,NodeMinus53.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3408.p3417,GridMinus.atNode 3417,GridMinus.atNode 3418,NodeMinus53.w25,CompactMinus3408.checked3417,CompactMinus3408.small3417,CompactMinus3408.nodes3417,NodeMinus53.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3408.p3418,GridMinus.atNode 3418,GridMinus.atNode 3419,NodeMinus53.w26,CompactMinus3408.checked3418,CompactMinus3408.small3418,CompactMinus3408.nodes3418,NodeMinus53.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3408.p3419,GridMinus.atNode 3419,GridMinus.atNode 3420,NodeMinus53.w27,CompactMinus3408.checked3419,CompactMinus3408.small3419,CompactMinus3408.nodes3419,NodeMinus53.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3408.p3420,GridMinus.atNode 3420,GridMinus.atNode 3421,NodeMinus53.w28,CompactMinus3408.checked3420,CompactMinus3408.small3420,CompactMinus3408.nodes3420,NodeMinus53.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3408.p3421,GridMinus.atNode 3421,GridMinus.atNode 3422,NodeMinus53.w29,CompactMinus3408.checked3421,CompactMinus3408.small3421,CompactMinus3408.nodes3421,NodeMinus53.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3408.p3422,GridMinus.atNode 3422,GridMinus.atNode 3423,NodeMinus53.w30,CompactMinus3408.checked3422,CompactMinus3408.small3422,CompactMinus3408.nodes3422,NodeMinus53.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3408.p3423,GridMinus.atNode 3423,GridMinus.atNode 3424,NodeMinus53.w31,CompactMinus3408.checked3423,CompactMinus3408.small3423,CompactMinus3408.nodes3423,NodeMinus53.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3424.p3424,GridMinus.atNode 3424,GridMinus.atNode 3425,NodeMinus53.w32,CompactMinus3424.checked3424,CompactMinus3424.small3424,CompactMinus3424.nodes3424,NodeMinus53.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3424.p3425,GridMinus.atNode 3425,GridMinus.atNode 3426,NodeMinus53.w33,CompactMinus3424.checked3425,CompactMinus3424.small3425,CompactMinus3424.nodes3425,NodeMinus53.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3424.p3426,GridMinus.atNode 3426,GridMinus.atNode 3427,NodeMinus53.w34,CompactMinus3424.checked3426,CompactMinus3424.small3426,CompactMinus3424.nodes3426,NodeMinus53.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3424.p3427,GridMinus.atNode 3427,GridMinus.atNode 3428,NodeMinus53.w35,CompactMinus3424.checked3427,CompactMinus3424.small3427,CompactMinus3424.nodes3427,NodeMinus53.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3424.p3428,GridMinus.atNode 3428,GridMinus.atNode 3429,NodeMinus53.w36,CompactMinus3424.checked3428,CompactMinus3424.small3428,CompactMinus3424.nodes3428,NodeMinus53.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3424.p3429,GridMinus.atNode 3429,GridMinus.atNode 3430,NodeMinus53.w37,CompactMinus3424.checked3429,CompactMinus3424.small3429,CompactMinus3424.nodes3429,NodeMinus53.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3424.p3430,GridMinus.atNode 3430,GridMinus.atNode 3431,NodeMinus53.w38,CompactMinus3424.checked3430,CompactMinus3424.small3430,CompactMinus3424.nodes3430,NodeMinus53.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3424.p3431,GridMinus.atNode 3431,GridMinus.atNode 3432,NodeMinus53.w39,CompactMinus3424.checked3431,CompactMinus3424.small3431,CompactMinus3424.nodes3431,NodeMinus53.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3424.p3432,GridMinus.atNode 3432,GridMinus.atNode 3433,NodeMinus53.w40,CompactMinus3424.checked3432,CompactMinus3424.small3432,CompactMinus3424.nodes3432,NodeMinus53.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3424.p3433,GridMinus.atNode 3433,GridMinus.atNode 3434,NodeMinus53.w41,CompactMinus3424.checked3433,CompactMinus3424.small3433,CompactMinus3424.nodes3433,NodeMinus53.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3424.p3434,GridMinus.atNode 3434,GridMinus.atNode 3435,NodeMinus53.w42,CompactMinus3424.checked3434,CompactMinus3424.small3434,CompactMinus3424.nodes3434,NodeMinus53.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3424.p3435,GridMinus.atNode 3435,GridMinus.atNode 3436,NodeMinus53.w43,CompactMinus3424.checked3435,CompactMinus3424.small3435,CompactMinus3424.nodes3435,NodeMinus53.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3424.p3436,GridMinus.atNode 3436,GridMinus.atNode 3437,NodeMinus53.w44,CompactMinus3424.checked3436,CompactMinus3424.small3436,CompactMinus3424.nodes3436,NodeMinus53.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3424.p3437,GridMinus.atNode 3437,GridMinus.atNode 3438,NodeMinus53.w45,CompactMinus3424.checked3437,CompactMinus3424.small3437,CompactMinus3424.nodes3437,NodeMinus53.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3424.p3438,GridMinus.atNode 3438,GridMinus.atNode 3439,NodeMinus53.w46,CompactMinus3424.checked3438,CompactMinus3424.small3438,CompactMinus3424.nodes3438,NodeMinus53.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3424.p3439,GridMinus.atNode 3439,GridMinus.atNode 3440,NodeMinus53.w47,CompactMinus3424.checked3439,CompactMinus3424.small3439,CompactMinus3424.nodes3439,NodeMinus53.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3440.p3440,GridMinus.atNode 3440,GridMinus.atNode 3441,NodeMinus53.w48,CompactMinus3440.checked3440,CompactMinus3440.small3440,CompactMinus3440.nodes3440,NodeMinus53.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3440.p3441,GridMinus.atNode 3441,GridMinus.atNode 3442,NodeMinus53.w49,CompactMinus3440.checked3441,CompactMinus3440.small3441,CompactMinus3440.nodes3441,NodeMinus53.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3440.p3442,GridMinus.atNode 3442,GridMinus.atNode 3443,NodeMinus53.w50,CompactMinus3440.checked3442,CompactMinus3440.small3442,CompactMinus3440.nodes3442,NodeMinus53.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3440.p3443,GridMinus.atNode 3443,GridMinus.atNode 3444,NodeMinus53.w51,CompactMinus3440.checked3443,CompactMinus3440.small3443,CompactMinus3440.nodes3443,NodeMinus53.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3440.p3444,GridMinus.atNode 3444,GridMinus.atNode 3445,NodeMinus53.w52,CompactMinus3440.checked3444,CompactMinus3440.small3444,CompactMinus3440.nodes3444,NodeMinus53.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3440.p3445,GridMinus.atNode 3445,GridMinus.atNode 3446,NodeMinus53.w53,CompactMinus3440.checked3445,CompactMinus3440.small3445,CompactMinus3440.nodes3445,NodeMinus53.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3440.p3446,GridMinus.atNode 3446,GridMinus.atNode 3447,NodeMinus53.w54,CompactMinus3440.checked3446,CompactMinus3440.small3446,CompactMinus3440.nodes3446,NodeMinus53.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3440.p3447,GridMinus.atNode 3447,GridMinus.atNode 3448,NodeMinus53.w55,CompactMinus3440.checked3447,CompactMinus3440.small3447,CompactMinus3440.nodes3447,NodeMinus53.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3440.p3448,GridMinus.atNode 3448,GridMinus.atNode 3449,NodeMinus53.w56,CompactMinus3440.checked3448,CompactMinus3440.small3448,CompactMinus3440.nodes3448,NodeMinus53.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3440.p3449,GridMinus.atNode 3449,GridMinus.atNode 3450,NodeMinus53.w57,CompactMinus3440.checked3449,CompactMinus3440.small3449,CompactMinus3440.nodes3449,NodeMinus53.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3440.p3450,GridMinus.atNode 3450,GridMinus.atNode 3451,NodeMinus53.w58,CompactMinus3440.checked3450,CompactMinus3440.small3450,CompactMinus3440.nodes3450,NodeMinus53.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3440.p3451,GridMinus.atNode 3451,GridMinus.atNode 3452,NodeMinus53.w59,CompactMinus3440.checked3451,CompactMinus3440.small3451,CompactMinus3440.nodes3451,NodeMinus53.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3440.p3452,GridMinus.atNode 3452,GridMinus.atNode 3453,NodeMinus53.w60,CompactMinus3440.checked3452,CompactMinus3440.small3452,CompactMinus3440.nodes3452,NodeMinus53.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3440.p3453,GridMinus.atNode 3453,GridMinus.atNode 3454,NodeMinus53.w61,CompactMinus3440.checked3453,CompactMinus3440.small3453,CompactMinus3440.nodes3453,NodeMinus53.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3440.p3454,GridMinus.atNode 3454,GridMinus.atNode 3455,NodeMinus53.w62,CompactMinus3440.checked3454,CompactMinus3440.small3454,CompactMinus3440.nodes3454,NodeMinus53.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3440.p3455,GridMinus.atNode 3455,GridMinus.atNode 3456,NodeMinus53.w63,CompactMinus3440.checked3455,CompactMinus3440.small3455,CompactMinus3440.nodes3455,NodeMinus53.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (3392+j) ∧
    (atRow j).right=GridMinus.atNode (3392+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus53
