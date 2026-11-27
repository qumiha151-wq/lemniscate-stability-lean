import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus3456
import SolitonClassification.Rotating.ResetPackedMinus3472
import SolitonClassification.Rotating.ResetPackedMinus3488
import SolitonClassification.Rotating.ResetPackedMinus3504
namespace SolitonClassification.Rotating.DyadicReset.TileMinus54
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3456.p3456,GridMinus.atNode 3456,GridMinus.atNode 3457,NodeMinus54.w0,CompactMinus3456.checked3456,CompactMinus3456.small3456,CompactMinus3456.nodes3456,NodeMinus54.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3456.p3457,GridMinus.atNode 3457,GridMinus.atNode 3458,NodeMinus54.w1,CompactMinus3456.checked3457,CompactMinus3456.small3457,CompactMinus3456.nodes3457,NodeMinus54.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3456.p3458,GridMinus.atNode 3458,GridMinus.atNode 3459,NodeMinus54.w2,CompactMinus3456.checked3458,CompactMinus3456.small3458,CompactMinus3456.nodes3458,NodeMinus54.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3456.p3459,GridMinus.atNode 3459,GridMinus.atNode 3460,NodeMinus54.w3,CompactMinus3456.checked3459,CompactMinus3456.small3459,CompactMinus3456.nodes3459,NodeMinus54.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3456.p3460,GridMinus.atNode 3460,GridMinus.atNode 3461,NodeMinus54.w4,CompactMinus3456.checked3460,CompactMinus3456.small3460,CompactMinus3456.nodes3460,NodeMinus54.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3456.p3461,GridMinus.atNode 3461,GridMinus.atNode 3462,NodeMinus54.w5,CompactMinus3456.checked3461,CompactMinus3456.small3461,CompactMinus3456.nodes3461,NodeMinus54.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3456.p3462,GridMinus.atNode 3462,GridMinus.atNode 3463,NodeMinus54.w6,CompactMinus3456.checked3462,CompactMinus3456.small3462,CompactMinus3456.nodes3462,NodeMinus54.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3456.p3463,GridMinus.atNode 3463,GridMinus.atNode 3464,NodeMinus54.w7,CompactMinus3456.checked3463,CompactMinus3456.small3463,CompactMinus3456.nodes3463,NodeMinus54.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3456.p3464,GridMinus.atNode 3464,GridMinus.atNode 3465,NodeMinus54.w8,CompactMinus3456.checked3464,CompactMinus3456.small3464,CompactMinus3456.nodes3464,NodeMinus54.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3456.p3465,GridMinus.atNode 3465,GridMinus.atNode 3466,NodeMinus54.w9,CompactMinus3456.checked3465,CompactMinus3456.small3465,CompactMinus3456.nodes3465,NodeMinus54.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3456.p3466,GridMinus.atNode 3466,GridMinus.atNode 3467,NodeMinus54.w10,CompactMinus3456.checked3466,CompactMinus3456.small3466,CompactMinus3456.nodes3466,NodeMinus54.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3456.p3467,GridMinus.atNode 3467,GridMinus.atNode 3468,NodeMinus54.w11,CompactMinus3456.checked3467,CompactMinus3456.small3467,CompactMinus3456.nodes3467,NodeMinus54.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3456.p3468,GridMinus.atNode 3468,GridMinus.atNode 3469,NodeMinus54.w12,CompactMinus3456.checked3468,CompactMinus3456.small3468,CompactMinus3456.nodes3468,NodeMinus54.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3456.p3469,GridMinus.atNode 3469,GridMinus.atNode 3470,NodeMinus54.w13,CompactMinus3456.checked3469,CompactMinus3456.small3469,CompactMinus3456.nodes3469,NodeMinus54.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3456.p3470,GridMinus.atNode 3470,GridMinus.atNode 3471,NodeMinus54.w14,CompactMinus3456.checked3470,CompactMinus3456.small3470,CompactMinus3456.nodes3470,NodeMinus54.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3456.p3471,GridMinus.atNode 3471,GridMinus.atNode 3472,NodeMinus54.w15,CompactMinus3456.checked3471,CompactMinus3456.small3471,CompactMinus3456.nodes3471,NodeMinus54.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3472.p3472,GridMinus.atNode 3472,GridMinus.atNode 3473,NodeMinus54.w16,CompactMinus3472.checked3472,CompactMinus3472.small3472,CompactMinus3472.nodes3472,NodeMinus54.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3472.p3473,GridMinus.atNode 3473,GridMinus.atNode 3474,NodeMinus54.w17,CompactMinus3472.checked3473,CompactMinus3472.small3473,CompactMinus3472.nodes3473,NodeMinus54.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3472.p3474,GridMinus.atNode 3474,GridMinus.atNode 3475,NodeMinus54.w18,CompactMinus3472.checked3474,CompactMinus3472.small3474,CompactMinus3472.nodes3474,NodeMinus54.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3472.p3475,GridMinus.atNode 3475,GridMinus.atNode 3476,NodeMinus54.w19,CompactMinus3472.checked3475,CompactMinus3472.small3475,CompactMinus3472.nodes3475,NodeMinus54.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3472.p3476,GridMinus.atNode 3476,GridMinus.atNode 3477,NodeMinus54.w20,CompactMinus3472.checked3476,CompactMinus3472.small3476,CompactMinus3472.nodes3476,NodeMinus54.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3472.p3477,GridMinus.atNode 3477,GridMinus.atNode 3478,NodeMinus54.w21,CompactMinus3472.checked3477,CompactMinus3472.small3477,CompactMinus3472.nodes3477,NodeMinus54.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3472.p3478,GridMinus.atNode 3478,GridMinus.atNode 3479,NodeMinus54.w22,CompactMinus3472.checked3478,CompactMinus3472.small3478,CompactMinus3472.nodes3478,NodeMinus54.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3472.p3479,GridMinus.atNode 3479,GridMinus.atNode 3480,NodeMinus54.w23,CompactMinus3472.checked3479,CompactMinus3472.small3479,CompactMinus3472.nodes3479,NodeMinus54.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3472.p3480,GridMinus.atNode 3480,GridMinus.atNode 3481,NodeMinus54.w24,CompactMinus3472.checked3480,CompactMinus3472.small3480,CompactMinus3472.nodes3480,NodeMinus54.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3472.p3481,GridMinus.atNode 3481,GridMinus.atNode 3482,NodeMinus54.w25,CompactMinus3472.checked3481,CompactMinus3472.small3481,CompactMinus3472.nodes3481,NodeMinus54.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3472.p3482,GridMinus.atNode 3482,GridMinus.atNode 3483,NodeMinus54.w26,CompactMinus3472.checked3482,CompactMinus3472.small3482,CompactMinus3472.nodes3482,NodeMinus54.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3472.p3483,GridMinus.atNode 3483,GridMinus.atNode 3484,NodeMinus54.w27,CompactMinus3472.checked3483,CompactMinus3472.small3483,CompactMinus3472.nodes3483,NodeMinus54.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3472.p3484,GridMinus.atNode 3484,GridMinus.atNode 3485,NodeMinus54.w28,CompactMinus3472.checked3484,CompactMinus3472.small3484,CompactMinus3472.nodes3484,NodeMinus54.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3472.p3485,GridMinus.atNode 3485,GridMinus.atNode 3486,NodeMinus54.w29,CompactMinus3472.checked3485,CompactMinus3472.small3485,CompactMinus3472.nodes3485,NodeMinus54.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3472.p3486,GridMinus.atNode 3486,GridMinus.atNode 3487,NodeMinus54.w30,CompactMinus3472.checked3486,CompactMinus3472.small3486,CompactMinus3472.nodes3486,NodeMinus54.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3472.p3487,GridMinus.atNode 3487,GridMinus.atNode 3488,NodeMinus54.w31,CompactMinus3472.checked3487,CompactMinus3472.small3487,CompactMinus3472.nodes3487,NodeMinus54.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3488.p3488,GridMinus.atNode 3488,GridMinus.atNode 3489,NodeMinus54.w32,CompactMinus3488.checked3488,CompactMinus3488.small3488,CompactMinus3488.nodes3488,NodeMinus54.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3488.p3489,GridMinus.atNode 3489,GridMinus.atNode 3490,NodeMinus54.w33,CompactMinus3488.checked3489,CompactMinus3488.small3489,CompactMinus3488.nodes3489,NodeMinus54.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3488.p3490,GridMinus.atNode 3490,GridMinus.atNode 3491,NodeMinus54.w34,CompactMinus3488.checked3490,CompactMinus3488.small3490,CompactMinus3488.nodes3490,NodeMinus54.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3488.p3491,GridMinus.atNode 3491,GridMinus.atNode 3492,NodeMinus54.w35,CompactMinus3488.checked3491,CompactMinus3488.small3491,CompactMinus3488.nodes3491,NodeMinus54.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3488.p3492,GridMinus.atNode 3492,GridMinus.atNode 3493,NodeMinus54.w36,CompactMinus3488.checked3492,CompactMinus3488.small3492,CompactMinus3488.nodes3492,NodeMinus54.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3488.p3493,GridMinus.atNode 3493,GridMinus.atNode 3494,NodeMinus54.w37,CompactMinus3488.checked3493,CompactMinus3488.small3493,CompactMinus3488.nodes3493,NodeMinus54.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3488.p3494,GridMinus.atNode 3494,GridMinus.atNode 3495,NodeMinus54.w38,CompactMinus3488.checked3494,CompactMinus3488.small3494,CompactMinus3488.nodes3494,NodeMinus54.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3488.p3495,GridMinus.atNode 3495,GridMinus.atNode 3496,NodeMinus54.w39,CompactMinus3488.checked3495,CompactMinus3488.small3495,CompactMinus3488.nodes3495,NodeMinus54.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3488.p3496,GridMinus.atNode 3496,GridMinus.atNode 3497,NodeMinus54.w40,CompactMinus3488.checked3496,CompactMinus3488.small3496,CompactMinus3488.nodes3496,NodeMinus54.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3488.p3497,GridMinus.atNode 3497,GridMinus.atNode 3498,NodeMinus54.w41,CompactMinus3488.checked3497,CompactMinus3488.small3497,CompactMinus3488.nodes3497,NodeMinus54.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3488.p3498,GridMinus.atNode 3498,GridMinus.atNode 3499,NodeMinus54.w42,CompactMinus3488.checked3498,CompactMinus3488.small3498,CompactMinus3488.nodes3498,NodeMinus54.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3488.p3499,GridMinus.atNode 3499,GridMinus.atNode 3500,NodeMinus54.w43,CompactMinus3488.checked3499,CompactMinus3488.small3499,CompactMinus3488.nodes3499,NodeMinus54.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3488.p3500,GridMinus.atNode 3500,GridMinus.atNode 3501,NodeMinus54.w44,CompactMinus3488.checked3500,CompactMinus3488.small3500,CompactMinus3488.nodes3500,NodeMinus54.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3488.p3501,GridMinus.atNode 3501,GridMinus.atNode 3502,NodeMinus54.w45,CompactMinus3488.checked3501,CompactMinus3488.small3501,CompactMinus3488.nodes3501,NodeMinus54.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3488.p3502,GridMinus.atNode 3502,GridMinus.atNode 3503,NodeMinus54.w46,CompactMinus3488.checked3502,CompactMinus3488.small3502,CompactMinus3488.nodes3502,NodeMinus54.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3488.p3503,GridMinus.atNode 3503,GridMinus.atNode 3504,NodeMinus54.w47,CompactMinus3488.checked3503,CompactMinus3488.small3503,CompactMinus3488.nodes3503,NodeMinus54.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3504.p3504,GridMinus.atNode 3504,GridMinus.atNode 3505,NodeMinus54.w48,CompactMinus3504.checked3504,CompactMinus3504.small3504,CompactMinus3504.nodes3504,NodeMinus54.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3504.p3505,GridMinus.atNode 3505,GridMinus.atNode 3506,NodeMinus54.w49,CompactMinus3504.checked3505,CompactMinus3504.small3505,CompactMinus3504.nodes3505,NodeMinus54.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3504.p3506,GridMinus.atNode 3506,GridMinus.atNode 3507,NodeMinus54.w50,CompactMinus3504.checked3506,CompactMinus3504.small3506,CompactMinus3504.nodes3506,NodeMinus54.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3504.p3507,GridMinus.atNode 3507,GridMinus.atNode 3508,NodeMinus54.w51,CompactMinus3504.checked3507,CompactMinus3504.small3507,CompactMinus3504.nodes3507,NodeMinus54.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3504.p3508,GridMinus.atNode 3508,GridMinus.atNode 3509,NodeMinus54.w52,CompactMinus3504.checked3508,CompactMinus3504.small3508,CompactMinus3504.nodes3508,NodeMinus54.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3504.p3509,GridMinus.atNode 3509,GridMinus.atNode 3510,NodeMinus54.w53,CompactMinus3504.checked3509,CompactMinus3504.small3509,CompactMinus3504.nodes3509,NodeMinus54.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3504.p3510,GridMinus.atNode 3510,GridMinus.atNode 3511,NodeMinus54.w54,CompactMinus3504.checked3510,CompactMinus3504.small3510,CompactMinus3504.nodes3510,NodeMinus54.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3504.p3511,GridMinus.atNode 3511,GridMinus.atNode 3512,NodeMinus54.w55,CompactMinus3504.checked3511,CompactMinus3504.small3511,CompactMinus3504.nodes3511,NodeMinus54.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3504.p3512,GridMinus.atNode 3512,GridMinus.atNode 3513,NodeMinus54.w56,CompactMinus3504.checked3512,CompactMinus3504.small3512,CompactMinus3504.nodes3512,NodeMinus54.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3504.p3513,GridMinus.atNode 3513,GridMinus.atNode 3514,NodeMinus54.w57,CompactMinus3504.checked3513,CompactMinus3504.small3513,CompactMinus3504.nodes3513,NodeMinus54.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3504.p3514,GridMinus.atNode 3514,GridMinus.atNode 3515,NodeMinus54.w58,CompactMinus3504.checked3514,CompactMinus3504.small3514,CompactMinus3504.nodes3514,NodeMinus54.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3504.p3515,GridMinus.atNode 3515,GridMinus.atNode 3516,NodeMinus54.w59,CompactMinus3504.checked3515,CompactMinus3504.small3515,CompactMinus3504.nodes3515,NodeMinus54.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3504.p3516,GridMinus.atNode 3516,GridMinus.atNode 3517,NodeMinus54.w60,CompactMinus3504.checked3516,CompactMinus3504.small3516,CompactMinus3504.nodes3516,NodeMinus54.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3504.p3517,GridMinus.atNode 3517,GridMinus.atNode 3518,NodeMinus54.w61,CompactMinus3504.checked3517,CompactMinus3504.small3517,CompactMinus3504.nodes3517,NodeMinus54.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3504.p3518,GridMinus.atNode 3518,GridMinus.atNode 3519,NodeMinus54.w62,CompactMinus3504.checked3518,CompactMinus3504.small3518,CompactMinus3504.nodes3518,NodeMinus54.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3504.p3519,GridMinus.atNode 3519,GridMinus.atNode 3520,NodeMinus54.w63,CompactMinus3504.checked3519,CompactMinus3504.small3519,CompactMinus3504.nodes3519,NodeMinus54.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (3456+j) ∧
    (atRow j).right=GridMinus.atNode (3456+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus54
