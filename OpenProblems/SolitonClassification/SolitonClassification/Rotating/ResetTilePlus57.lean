import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus3648
import SolitonClassification.Rotating.ResetPackedPlus3664
import SolitonClassification.Rotating.ResetPackedPlus3680
import SolitonClassification.Rotating.ResetPackedPlus3696
namespace SolitonClassification.Rotating.DyadicReset.TilePlus57
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus3648.p3648,GridPlus.atNode 3648,GridPlus.atNode 3649,NodePlus57.w0,CompactPlus3648.checked3648,CompactPlus3648.small3648,CompactPlus3648.nodes3648,NodePlus57.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus3648.p3649,GridPlus.atNode 3649,GridPlus.atNode 3650,NodePlus57.w1,CompactPlus3648.checked3649,CompactPlus3648.small3649,CompactPlus3648.nodes3649,NodePlus57.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus3648.p3650,GridPlus.atNode 3650,GridPlus.atNode 3651,NodePlus57.w2,CompactPlus3648.checked3650,CompactPlus3648.small3650,CompactPlus3648.nodes3650,NodePlus57.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus3648.p3651,GridPlus.atNode 3651,GridPlus.atNode 3652,NodePlus57.w3,CompactPlus3648.checked3651,CompactPlus3648.small3651,CompactPlus3648.nodes3651,NodePlus57.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus3648.p3652,GridPlus.atNode 3652,GridPlus.atNode 3653,NodePlus57.w4,CompactPlus3648.checked3652,CompactPlus3648.small3652,CompactPlus3648.nodes3652,NodePlus57.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus3648.p3653,GridPlus.atNode 3653,GridPlus.atNode 3654,NodePlus57.w5,CompactPlus3648.checked3653,CompactPlus3648.small3653,CompactPlus3648.nodes3653,NodePlus57.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus3648.p3654,GridPlus.atNode 3654,GridPlus.atNode 3655,NodePlus57.w6,CompactPlus3648.checked3654,CompactPlus3648.small3654,CompactPlus3648.nodes3654,NodePlus57.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus3648.p3655,GridPlus.atNode 3655,GridPlus.atNode 3656,NodePlus57.w7,CompactPlus3648.checked3655,CompactPlus3648.small3655,CompactPlus3648.nodes3655,NodePlus57.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus3648.p3656,GridPlus.atNode 3656,GridPlus.atNode 3657,NodePlus57.w8,CompactPlus3648.checked3656,CompactPlus3648.small3656,CompactPlus3648.nodes3656,NodePlus57.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus3648.p3657,GridPlus.atNode 3657,GridPlus.atNode 3658,NodePlus57.w9,CompactPlus3648.checked3657,CompactPlus3648.small3657,CompactPlus3648.nodes3657,NodePlus57.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus3648.p3658,GridPlus.atNode 3658,GridPlus.atNode 3659,NodePlus57.w10,CompactPlus3648.checked3658,CompactPlus3648.small3658,CompactPlus3648.nodes3658,NodePlus57.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus3648.p3659,GridPlus.atNode 3659,GridPlus.atNode 3660,NodePlus57.w11,CompactPlus3648.checked3659,CompactPlus3648.small3659,CompactPlus3648.nodes3659,NodePlus57.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus3648.p3660,GridPlus.atNode 3660,GridPlus.atNode 3661,NodePlus57.w12,CompactPlus3648.checked3660,CompactPlus3648.small3660,CompactPlus3648.nodes3660,NodePlus57.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus3648.p3661,GridPlus.atNode 3661,GridPlus.atNode 3662,NodePlus57.w13,CompactPlus3648.checked3661,CompactPlus3648.small3661,CompactPlus3648.nodes3661,NodePlus57.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus3648.p3662,GridPlus.atNode 3662,GridPlus.atNode 3663,NodePlus57.w14,CompactPlus3648.checked3662,CompactPlus3648.small3662,CompactPlus3648.nodes3662,NodePlus57.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus3648.p3663,GridPlus.atNode 3663,GridPlus.atNode 3664,NodePlus57.w15,CompactPlus3648.checked3663,CompactPlus3648.small3663,CompactPlus3648.nodes3663,NodePlus57.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus3664.p3664,GridPlus.atNode 3664,GridPlus.atNode 3665,NodePlus57.w16,CompactPlus3664.checked3664,CompactPlus3664.small3664,CompactPlus3664.nodes3664,NodePlus57.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus3664.p3665,GridPlus.atNode 3665,GridPlus.atNode 3666,NodePlus57.w17,CompactPlus3664.checked3665,CompactPlus3664.small3665,CompactPlus3664.nodes3665,NodePlus57.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus3664.p3666,GridPlus.atNode 3666,GridPlus.atNode 3667,NodePlus57.w18,CompactPlus3664.checked3666,CompactPlus3664.small3666,CompactPlus3664.nodes3666,NodePlus57.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus3664.p3667,GridPlus.atNode 3667,GridPlus.atNode 3668,NodePlus57.w19,CompactPlus3664.checked3667,CompactPlus3664.small3667,CompactPlus3664.nodes3667,NodePlus57.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus3664.p3668,GridPlus.atNode 3668,GridPlus.atNode 3669,NodePlus57.w20,CompactPlus3664.checked3668,CompactPlus3664.small3668,CompactPlus3664.nodes3668,NodePlus57.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus3664.p3669,GridPlus.atNode 3669,GridPlus.atNode 3670,NodePlus57.w21,CompactPlus3664.checked3669,CompactPlus3664.small3669,CompactPlus3664.nodes3669,NodePlus57.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus3664.p3670,GridPlus.atNode 3670,GridPlus.atNode 3671,NodePlus57.w22,CompactPlus3664.checked3670,CompactPlus3664.small3670,CompactPlus3664.nodes3670,NodePlus57.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus3664.p3671,GridPlus.atNode 3671,GridPlus.atNode 3672,NodePlus57.w23,CompactPlus3664.checked3671,CompactPlus3664.small3671,CompactPlus3664.nodes3671,NodePlus57.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus3664.p3672,GridPlus.atNode 3672,GridPlus.atNode 3673,NodePlus57.w24,CompactPlus3664.checked3672,CompactPlus3664.small3672,CompactPlus3664.nodes3672,NodePlus57.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus3664.p3673,GridPlus.atNode 3673,GridPlus.atNode 3674,NodePlus57.w25,CompactPlus3664.checked3673,CompactPlus3664.small3673,CompactPlus3664.nodes3673,NodePlus57.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus3664.p3674,GridPlus.atNode 3674,GridPlus.atNode 3675,NodePlus57.w26,CompactPlus3664.checked3674,CompactPlus3664.small3674,CompactPlus3664.nodes3674,NodePlus57.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus3664.p3675,GridPlus.atNode 3675,GridPlus.atNode 3676,NodePlus57.w27,CompactPlus3664.checked3675,CompactPlus3664.small3675,CompactPlus3664.nodes3675,NodePlus57.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus3664.p3676,GridPlus.atNode 3676,GridPlus.atNode 3677,NodePlus57.w28,CompactPlus3664.checked3676,CompactPlus3664.small3676,CompactPlus3664.nodes3676,NodePlus57.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus3664.p3677,GridPlus.atNode 3677,GridPlus.atNode 3678,NodePlus57.w29,CompactPlus3664.checked3677,CompactPlus3664.small3677,CompactPlus3664.nodes3677,NodePlus57.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus3664.p3678,GridPlus.atNode 3678,GridPlus.atNode 3679,NodePlus57.w30,CompactPlus3664.checked3678,CompactPlus3664.small3678,CompactPlus3664.nodes3678,NodePlus57.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus3664.p3679,GridPlus.atNode 3679,GridPlus.atNode 3680,NodePlus57.w31,CompactPlus3664.checked3679,CompactPlus3664.small3679,CompactPlus3664.nodes3679,NodePlus57.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus3680.p3680,GridPlus.atNode 3680,GridPlus.atNode 3681,NodePlus57.w32,CompactPlus3680.checked3680,CompactPlus3680.small3680,CompactPlus3680.nodes3680,NodePlus57.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus3680.p3681,GridPlus.atNode 3681,GridPlus.atNode 3682,NodePlus57.w33,CompactPlus3680.checked3681,CompactPlus3680.small3681,CompactPlus3680.nodes3681,NodePlus57.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus3680.p3682,GridPlus.atNode 3682,GridPlus.atNode 3683,NodePlus57.w34,CompactPlus3680.checked3682,CompactPlus3680.small3682,CompactPlus3680.nodes3682,NodePlus57.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus3680.p3683,GridPlus.atNode 3683,GridPlus.atNode 3684,NodePlus57.w35,CompactPlus3680.checked3683,CompactPlus3680.small3683,CompactPlus3680.nodes3683,NodePlus57.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus3680.p3684,GridPlus.atNode 3684,GridPlus.atNode 3685,NodePlus57.w36,CompactPlus3680.checked3684,CompactPlus3680.small3684,CompactPlus3680.nodes3684,NodePlus57.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus3680.p3685,GridPlus.atNode 3685,GridPlus.atNode 3686,NodePlus57.w37,CompactPlus3680.checked3685,CompactPlus3680.small3685,CompactPlus3680.nodes3685,NodePlus57.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus3680.p3686,GridPlus.atNode 3686,GridPlus.atNode 3687,NodePlus57.w38,CompactPlus3680.checked3686,CompactPlus3680.small3686,CompactPlus3680.nodes3686,NodePlus57.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus3680.p3687,GridPlus.atNode 3687,GridPlus.atNode 3688,NodePlus57.w39,CompactPlus3680.checked3687,CompactPlus3680.small3687,CompactPlus3680.nodes3687,NodePlus57.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus3680.p3688,GridPlus.atNode 3688,GridPlus.atNode 3689,NodePlus57.w40,CompactPlus3680.checked3688,CompactPlus3680.small3688,CompactPlus3680.nodes3688,NodePlus57.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus3680.p3689,GridPlus.atNode 3689,GridPlus.atNode 3690,NodePlus57.w41,CompactPlus3680.checked3689,CompactPlus3680.small3689,CompactPlus3680.nodes3689,NodePlus57.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus3680.p3690,GridPlus.atNode 3690,GridPlus.atNode 3691,NodePlus57.w42,CompactPlus3680.checked3690,CompactPlus3680.small3690,CompactPlus3680.nodes3690,NodePlus57.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus3680.p3691,GridPlus.atNode 3691,GridPlus.atNode 3692,NodePlus57.w43,CompactPlus3680.checked3691,CompactPlus3680.small3691,CompactPlus3680.nodes3691,NodePlus57.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus3680.p3692,GridPlus.atNode 3692,GridPlus.atNode 3693,NodePlus57.w44,CompactPlus3680.checked3692,CompactPlus3680.small3692,CompactPlus3680.nodes3692,NodePlus57.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus3680.p3693,GridPlus.atNode 3693,GridPlus.atNode 3694,NodePlus57.w45,CompactPlus3680.checked3693,CompactPlus3680.small3693,CompactPlus3680.nodes3693,NodePlus57.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus3680.p3694,GridPlus.atNode 3694,GridPlus.atNode 3695,NodePlus57.w46,CompactPlus3680.checked3694,CompactPlus3680.small3694,CompactPlus3680.nodes3694,NodePlus57.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus3680.p3695,GridPlus.atNode 3695,GridPlus.atNode 3696,NodePlus57.w47,CompactPlus3680.checked3695,CompactPlus3680.small3695,CompactPlus3680.nodes3695,NodePlus57.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus3696.p3696,GridPlus.atNode 3696,GridPlus.atNode 3697,NodePlus57.w48,CompactPlus3696.checked3696,CompactPlus3696.small3696,CompactPlus3696.nodes3696,NodePlus57.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus3696.p3697,GridPlus.atNode 3697,GridPlus.atNode 3698,NodePlus57.w49,CompactPlus3696.checked3697,CompactPlus3696.small3697,CompactPlus3696.nodes3697,NodePlus57.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus3696.p3698,GridPlus.atNode 3698,GridPlus.atNode 3699,NodePlus57.w50,CompactPlus3696.checked3698,CompactPlus3696.small3698,CompactPlus3696.nodes3698,NodePlus57.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus3696.p3699,GridPlus.atNode 3699,GridPlus.atNode 3700,NodePlus57.w51,CompactPlus3696.checked3699,CompactPlus3696.small3699,CompactPlus3696.nodes3699,NodePlus57.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus3696.p3700,GridPlus.atNode 3700,GridPlus.atNode 3701,NodePlus57.w52,CompactPlus3696.checked3700,CompactPlus3696.small3700,CompactPlus3696.nodes3700,NodePlus57.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus3696.p3701,GridPlus.atNode 3701,GridPlus.atNode 3702,NodePlus57.w53,CompactPlus3696.checked3701,CompactPlus3696.small3701,CompactPlus3696.nodes3701,NodePlus57.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus3696.p3702,GridPlus.atNode 3702,GridPlus.atNode 3703,NodePlus57.w54,CompactPlus3696.checked3702,CompactPlus3696.small3702,CompactPlus3696.nodes3702,NodePlus57.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus3696.p3703,GridPlus.atNode 3703,GridPlus.atNode 3704,NodePlus57.w55,CompactPlus3696.checked3703,CompactPlus3696.small3703,CompactPlus3696.nodes3703,NodePlus57.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus3696.p3704,GridPlus.atNode 3704,GridPlus.atNode 3705,NodePlus57.w56,CompactPlus3696.checked3704,CompactPlus3696.small3704,CompactPlus3696.nodes3704,NodePlus57.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus3696.p3705,GridPlus.atNode 3705,GridPlus.atNode 3706,NodePlus57.w57,CompactPlus3696.checked3705,CompactPlus3696.small3705,CompactPlus3696.nodes3705,NodePlus57.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus3696.p3706,GridPlus.atNode 3706,GridPlus.atNode 3707,NodePlus57.w58,CompactPlus3696.checked3706,CompactPlus3696.small3706,CompactPlus3696.nodes3706,NodePlus57.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus3696.p3707,GridPlus.atNode 3707,GridPlus.atNode 3708,NodePlus57.w59,CompactPlus3696.checked3707,CompactPlus3696.small3707,CompactPlus3696.nodes3707,NodePlus57.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus3696.p3708,GridPlus.atNode 3708,GridPlus.atNode 3709,NodePlus57.w60,CompactPlus3696.checked3708,CompactPlus3696.small3708,CompactPlus3696.nodes3708,NodePlus57.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus3696.p3709,GridPlus.atNode 3709,GridPlus.atNode 3710,NodePlus57.w61,CompactPlus3696.checked3709,CompactPlus3696.small3709,CompactPlus3696.nodes3709,NodePlus57.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus3696.p3710,GridPlus.atNode 3710,GridPlus.atNode 3711,NodePlus57.w62,CompactPlus3696.checked3710,CompactPlus3696.small3710,CompactPlus3696.nodes3710,NodePlus57.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus3696.p3711,GridPlus.atNode 3711,GridPlus.atNode 3712,NodePlus57.w63,CompactPlus3696.checked3711,CompactPlus3696.small3711,CompactPlus3696.nodes3711,NodePlus57.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (3648+j) ∧
    (atRow j).right=GridPlus.atNode (3648+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus57
