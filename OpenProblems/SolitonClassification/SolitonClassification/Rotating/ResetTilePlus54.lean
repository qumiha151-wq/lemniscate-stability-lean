import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus3456
import SolitonClassification.Rotating.ResetPackedPlus3472
import SolitonClassification.Rotating.ResetPackedPlus3488
import SolitonClassification.Rotating.ResetPackedPlus3504
namespace SolitonClassification.Rotating.DyadicReset.TilePlus54
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus3456.p3456,GridPlus.atNode 3456,GridPlus.atNode 3457,NodePlus54.w0,CompactPlus3456.checked3456,CompactPlus3456.small3456,CompactPlus3456.nodes3456,NodePlus54.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus3456.p3457,GridPlus.atNode 3457,GridPlus.atNode 3458,NodePlus54.w1,CompactPlus3456.checked3457,CompactPlus3456.small3457,CompactPlus3456.nodes3457,NodePlus54.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus3456.p3458,GridPlus.atNode 3458,GridPlus.atNode 3459,NodePlus54.w2,CompactPlus3456.checked3458,CompactPlus3456.small3458,CompactPlus3456.nodes3458,NodePlus54.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus3456.p3459,GridPlus.atNode 3459,GridPlus.atNode 3460,NodePlus54.w3,CompactPlus3456.checked3459,CompactPlus3456.small3459,CompactPlus3456.nodes3459,NodePlus54.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus3456.p3460,GridPlus.atNode 3460,GridPlus.atNode 3461,NodePlus54.w4,CompactPlus3456.checked3460,CompactPlus3456.small3460,CompactPlus3456.nodes3460,NodePlus54.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus3456.p3461,GridPlus.atNode 3461,GridPlus.atNode 3462,NodePlus54.w5,CompactPlus3456.checked3461,CompactPlus3456.small3461,CompactPlus3456.nodes3461,NodePlus54.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus3456.p3462,GridPlus.atNode 3462,GridPlus.atNode 3463,NodePlus54.w6,CompactPlus3456.checked3462,CompactPlus3456.small3462,CompactPlus3456.nodes3462,NodePlus54.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus3456.p3463,GridPlus.atNode 3463,GridPlus.atNode 3464,NodePlus54.w7,CompactPlus3456.checked3463,CompactPlus3456.small3463,CompactPlus3456.nodes3463,NodePlus54.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus3456.p3464,GridPlus.atNode 3464,GridPlus.atNode 3465,NodePlus54.w8,CompactPlus3456.checked3464,CompactPlus3456.small3464,CompactPlus3456.nodes3464,NodePlus54.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus3456.p3465,GridPlus.atNode 3465,GridPlus.atNode 3466,NodePlus54.w9,CompactPlus3456.checked3465,CompactPlus3456.small3465,CompactPlus3456.nodes3465,NodePlus54.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus3456.p3466,GridPlus.atNode 3466,GridPlus.atNode 3467,NodePlus54.w10,CompactPlus3456.checked3466,CompactPlus3456.small3466,CompactPlus3456.nodes3466,NodePlus54.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus3456.p3467,GridPlus.atNode 3467,GridPlus.atNode 3468,NodePlus54.w11,CompactPlus3456.checked3467,CompactPlus3456.small3467,CompactPlus3456.nodes3467,NodePlus54.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus3456.p3468,GridPlus.atNode 3468,GridPlus.atNode 3469,NodePlus54.w12,CompactPlus3456.checked3468,CompactPlus3456.small3468,CompactPlus3456.nodes3468,NodePlus54.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus3456.p3469,GridPlus.atNode 3469,GridPlus.atNode 3470,NodePlus54.w13,CompactPlus3456.checked3469,CompactPlus3456.small3469,CompactPlus3456.nodes3469,NodePlus54.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus3456.p3470,GridPlus.atNode 3470,GridPlus.atNode 3471,NodePlus54.w14,CompactPlus3456.checked3470,CompactPlus3456.small3470,CompactPlus3456.nodes3470,NodePlus54.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus3456.p3471,GridPlus.atNode 3471,GridPlus.atNode 3472,NodePlus54.w15,CompactPlus3456.checked3471,CompactPlus3456.small3471,CompactPlus3456.nodes3471,NodePlus54.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus3472.p3472,GridPlus.atNode 3472,GridPlus.atNode 3473,NodePlus54.w16,CompactPlus3472.checked3472,CompactPlus3472.small3472,CompactPlus3472.nodes3472,NodePlus54.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus3472.p3473,GridPlus.atNode 3473,GridPlus.atNode 3474,NodePlus54.w17,CompactPlus3472.checked3473,CompactPlus3472.small3473,CompactPlus3472.nodes3473,NodePlus54.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus3472.p3474,GridPlus.atNode 3474,GridPlus.atNode 3475,NodePlus54.w18,CompactPlus3472.checked3474,CompactPlus3472.small3474,CompactPlus3472.nodes3474,NodePlus54.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus3472.p3475,GridPlus.atNode 3475,GridPlus.atNode 3476,NodePlus54.w19,CompactPlus3472.checked3475,CompactPlus3472.small3475,CompactPlus3472.nodes3475,NodePlus54.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus3472.p3476,GridPlus.atNode 3476,GridPlus.atNode 3477,NodePlus54.w20,CompactPlus3472.checked3476,CompactPlus3472.small3476,CompactPlus3472.nodes3476,NodePlus54.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus3472.p3477,GridPlus.atNode 3477,GridPlus.atNode 3478,NodePlus54.w21,CompactPlus3472.checked3477,CompactPlus3472.small3477,CompactPlus3472.nodes3477,NodePlus54.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus3472.p3478,GridPlus.atNode 3478,GridPlus.atNode 3479,NodePlus54.w22,CompactPlus3472.checked3478,CompactPlus3472.small3478,CompactPlus3472.nodes3478,NodePlus54.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus3472.p3479,GridPlus.atNode 3479,GridPlus.atNode 3480,NodePlus54.w23,CompactPlus3472.checked3479,CompactPlus3472.small3479,CompactPlus3472.nodes3479,NodePlus54.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus3472.p3480,GridPlus.atNode 3480,GridPlus.atNode 3481,NodePlus54.w24,CompactPlus3472.checked3480,CompactPlus3472.small3480,CompactPlus3472.nodes3480,NodePlus54.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus3472.p3481,GridPlus.atNode 3481,GridPlus.atNode 3482,NodePlus54.w25,CompactPlus3472.checked3481,CompactPlus3472.small3481,CompactPlus3472.nodes3481,NodePlus54.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus3472.p3482,GridPlus.atNode 3482,GridPlus.atNode 3483,NodePlus54.w26,CompactPlus3472.checked3482,CompactPlus3472.small3482,CompactPlus3472.nodes3482,NodePlus54.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus3472.p3483,GridPlus.atNode 3483,GridPlus.atNode 3484,NodePlus54.w27,CompactPlus3472.checked3483,CompactPlus3472.small3483,CompactPlus3472.nodes3483,NodePlus54.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus3472.p3484,GridPlus.atNode 3484,GridPlus.atNode 3485,NodePlus54.w28,CompactPlus3472.checked3484,CompactPlus3472.small3484,CompactPlus3472.nodes3484,NodePlus54.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus3472.p3485,GridPlus.atNode 3485,GridPlus.atNode 3486,NodePlus54.w29,CompactPlus3472.checked3485,CompactPlus3472.small3485,CompactPlus3472.nodes3485,NodePlus54.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus3472.p3486,GridPlus.atNode 3486,GridPlus.atNode 3487,NodePlus54.w30,CompactPlus3472.checked3486,CompactPlus3472.small3486,CompactPlus3472.nodes3486,NodePlus54.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus3472.p3487,GridPlus.atNode 3487,GridPlus.atNode 3488,NodePlus54.w31,CompactPlus3472.checked3487,CompactPlus3472.small3487,CompactPlus3472.nodes3487,NodePlus54.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus3488.p3488,GridPlus.atNode 3488,GridPlus.atNode 3489,NodePlus54.w32,CompactPlus3488.checked3488,CompactPlus3488.small3488,CompactPlus3488.nodes3488,NodePlus54.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus3488.p3489,GridPlus.atNode 3489,GridPlus.atNode 3490,NodePlus54.w33,CompactPlus3488.checked3489,CompactPlus3488.small3489,CompactPlus3488.nodes3489,NodePlus54.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus3488.p3490,GridPlus.atNode 3490,GridPlus.atNode 3491,NodePlus54.w34,CompactPlus3488.checked3490,CompactPlus3488.small3490,CompactPlus3488.nodes3490,NodePlus54.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus3488.p3491,GridPlus.atNode 3491,GridPlus.atNode 3492,NodePlus54.w35,CompactPlus3488.checked3491,CompactPlus3488.small3491,CompactPlus3488.nodes3491,NodePlus54.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus3488.p3492,GridPlus.atNode 3492,GridPlus.atNode 3493,NodePlus54.w36,CompactPlus3488.checked3492,CompactPlus3488.small3492,CompactPlus3488.nodes3492,NodePlus54.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus3488.p3493,GridPlus.atNode 3493,GridPlus.atNode 3494,NodePlus54.w37,CompactPlus3488.checked3493,CompactPlus3488.small3493,CompactPlus3488.nodes3493,NodePlus54.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus3488.p3494,GridPlus.atNode 3494,GridPlus.atNode 3495,NodePlus54.w38,CompactPlus3488.checked3494,CompactPlus3488.small3494,CompactPlus3488.nodes3494,NodePlus54.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus3488.p3495,GridPlus.atNode 3495,GridPlus.atNode 3496,NodePlus54.w39,CompactPlus3488.checked3495,CompactPlus3488.small3495,CompactPlus3488.nodes3495,NodePlus54.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus3488.p3496,GridPlus.atNode 3496,GridPlus.atNode 3497,NodePlus54.w40,CompactPlus3488.checked3496,CompactPlus3488.small3496,CompactPlus3488.nodes3496,NodePlus54.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus3488.p3497,GridPlus.atNode 3497,GridPlus.atNode 3498,NodePlus54.w41,CompactPlus3488.checked3497,CompactPlus3488.small3497,CompactPlus3488.nodes3497,NodePlus54.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus3488.p3498,GridPlus.atNode 3498,GridPlus.atNode 3499,NodePlus54.w42,CompactPlus3488.checked3498,CompactPlus3488.small3498,CompactPlus3488.nodes3498,NodePlus54.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus3488.p3499,GridPlus.atNode 3499,GridPlus.atNode 3500,NodePlus54.w43,CompactPlus3488.checked3499,CompactPlus3488.small3499,CompactPlus3488.nodes3499,NodePlus54.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus3488.p3500,GridPlus.atNode 3500,GridPlus.atNode 3501,NodePlus54.w44,CompactPlus3488.checked3500,CompactPlus3488.small3500,CompactPlus3488.nodes3500,NodePlus54.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus3488.p3501,GridPlus.atNode 3501,GridPlus.atNode 3502,NodePlus54.w45,CompactPlus3488.checked3501,CompactPlus3488.small3501,CompactPlus3488.nodes3501,NodePlus54.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus3488.p3502,GridPlus.atNode 3502,GridPlus.atNode 3503,NodePlus54.w46,CompactPlus3488.checked3502,CompactPlus3488.small3502,CompactPlus3488.nodes3502,NodePlus54.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus3488.p3503,GridPlus.atNode 3503,GridPlus.atNode 3504,NodePlus54.w47,CompactPlus3488.checked3503,CompactPlus3488.small3503,CompactPlus3488.nodes3503,NodePlus54.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus3504.p3504,GridPlus.atNode 3504,GridPlus.atNode 3505,NodePlus54.w48,CompactPlus3504.checked3504,CompactPlus3504.small3504,CompactPlus3504.nodes3504,NodePlus54.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus3504.p3505,GridPlus.atNode 3505,GridPlus.atNode 3506,NodePlus54.w49,CompactPlus3504.checked3505,CompactPlus3504.small3505,CompactPlus3504.nodes3505,NodePlus54.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus3504.p3506,GridPlus.atNode 3506,GridPlus.atNode 3507,NodePlus54.w50,CompactPlus3504.checked3506,CompactPlus3504.small3506,CompactPlus3504.nodes3506,NodePlus54.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus3504.p3507,GridPlus.atNode 3507,GridPlus.atNode 3508,NodePlus54.w51,CompactPlus3504.checked3507,CompactPlus3504.small3507,CompactPlus3504.nodes3507,NodePlus54.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus3504.p3508,GridPlus.atNode 3508,GridPlus.atNode 3509,NodePlus54.w52,CompactPlus3504.checked3508,CompactPlus3504.small3508,CompactPlus3504.nodes3508,NodePlus54.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus3504.p3509,GridPlus.atNode 3509,GridPlus.atNode 3510,NodePlus54.w53,CompactPlus3504.checked3509,CompactPlus3504.small3509,CompactPlus3504.nodes3509,NodePlus54.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus3504.p3510,GridPlus.atNode 3510,GridPlus.atNode 3511,NodePlus54.w54,CompactPlus3504.checked3510,CompactPlus3504.small3510,CompactPlus3504.nodes3510,NodePlus54.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus3504.p3511,GridPlus.atNode 3511,GridPlus.atNode 3512,NodePlus54.w55,CompactPlus3504.checked3511,CompactPlus3504.small3511,CompactPlus3504.nodes3511,NodePlus54.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus3504.p3512,GridPlus.atNode 3512,GridPlus.atNode 3513,NodePlus54.w56,CompactPlus3504.checked3512,CompactPlus3504.small3512,CompactPlus3504.nodes3512,NodePlus54.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus3504.p3513,GridPlus.atNode 3513,GridPlus.atNode 3514,NodePlus54.w57,CompactPlus3504.checked3513,CompactPlus3504.small3513,CompactPlus3504.nodes3513,NodePlus54.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus3504.p3514,GridPlus.atNode 3514,GridPlus.atNode 3515,NodePlus54.w58,CompactPlus3504.checked3514,CompactPlus3504.small3514,CompactPlus3504.nodes3514,NodePlus54.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus3504.p3515,GridPlus.atNode 3515,GridPlus.atNode 3516,NodePlus54.w59,CompactPlus3504.checked3515,CompactPlus3504.small3515,CompactPlus3504.nodes3515,NodePlus54.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus3504.p3516,GridPlus.atNode 3516,GridPlus.atNode 3517,NodePlus54.w60,CompactPlus3504.checked3516,CompactPlus3504.small3516,CompactPlus3504.nodes3516,NodePlus54.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus3504.p3517,GridPlus.atNode 3517,GridPlus.atNode 3518,NodePlus54.w61,CompactPlus3504.checked3517,CompactPlus3504.small3517,CompactPlus3504.nodes3517,NodePlus54.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus3504.p3518,GridPlus.atNode 3518,GridPlus.atNode 3519,NodePlus54.w62,CompactPlus3504.checked3518,CompactPlus3504.small3518,CompactPlus3504.nodes3518,NodePlus54.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus3504.p3519,GridPlus.atNode 3519,GridPlus.atNode 3520,NodePlus54.w63,CompactPlus3504.checked3519,CompactPlus3504.small3519,CompactPlus3504.nodes3519,NodePlus54.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (3456+j) ∧
    (atRow j).right=GridPlus.atNode (3456+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus54
