import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus3776
import SolitonClassification.Rotating.ResetPackedPlus3792
import SolitonClassification.Rotating.ResetPackedPlus3808
import SolitonClassification.Rotating.ResetPackedPlus3824
namespace SolitonClassification.Rotating.DyadicReset.TilePlus59
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus3776.p3776,GridPlus.atNode 3776,GridPlus.atNode 3777,NodePlus59.w0,CompactPlus3776.checked3776,CompactPlus3776.small3776,CompactPlus3776.nodes3776,NodePlus59.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus3776.p3777,GridPlus.atNode 3777,GridPlus.atNode 3778,NodePlus59.w1,CompactPlus3776.checked3777,CompactPlus3776.small3777,CompactPlus3776.nodes3777,NodePlus59.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus3776.p3778,GridPlus.atNode 3778,GridPlus.atNode 3779,NodePlus59.w2,CompactPlus3776.checked3778,CompactPlus3776.small3778,CompactPlus3776.nodes3778,NodePlus59.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus3776.p3779,GridPlus.atNode 3779,GridPlus.atNode 3780,NodePlus59.w3,CompactPlus3776.checked3779,CompactPlus3776.small3779,CompactPlus3776.nodes3779,NodePlus59.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus3776.p3780,GridPlus.atNode 3780,GridPlus.atNode 3781,NodePlus59.w4,CompactPlus3776.checked3780,CompactPlus3776.small3780,CompactPlus3776.nodes3780,NodePlus59.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus3776.p3781,GridPlus.atNode 3781,GridPlus.atNode 3782,NodePlus59.w5,CompactPlus3776.checked3781,CompactPlus3776.small3781,CompactPlus3776.nodes3781,NodePlus59.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus3776.p3782,GridPlus.atNode 3782,GridPlus.atNode 3783,NodePlus59.w6,CompactPlus3776.checked3782,CompactPlus3776.small3782,CompactPlus3776.nodes3782,NodePlus59.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus3776.p3783,GridPlus.atNode 3783,GridPlus.atNode 3784,NodePlus59.w7,CompactPlus3776.checked3783,CompactPlus3776.small3783,CompactPlus3776.nodes3783,NodePlus59.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus3776.p3784,GridPlus.atNode 3784,GridPlus.atNode 3785,NodePlus59.w8,CompactPlus3776.checked3784,CompactPlus3776.small3784,CompactPlus3776.nodes3784,NodePlus59.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus3776.p3785,GridPlus.atNode 3785,GridPlus.atNode 3786,NodePlus59.w9,CompactPlus3776.checked3785,CompactPlus3776.small3785,CompactPlus3776.nodes3785,NodePlus59.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus3776.p3786,GridPlus.atNode 3786,GridPlus.atNode 3787,NodePlus59.w10,CompactPlus3776.checked3786,CompactPlus3776.small3786,CompactPlus3776.nodes3786,NodePlus59.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus3776.p3787,GridPlus.atNode 3787,GridPlus.atNode 3788,NodePlus59.w11,CompactPlus3776.checked3787,CompactPlus3776.small3787,CompactPlus3776.nodes3787,NodePlus59.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus3776.p3788,GridPlus.atNode 3788,GridPlus.atNode 3789,NodePlus59.w12,CompactPlus3776.checked3788,CompactPlus3776.small3788,CompactPlus3776.nodes3788,NodePlus59.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus3776.p3789,GridPlus.atNode 3789,GridPlus.atNode 3790,NodePlus59.w13,CompactPlus3776.checked3789,CompactPlus3776.small3789,CompactPlus3776.nodes3789,NodePlus59.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus3776.p3790,GridPlus.atNode 3790,GridPlus.atNode 3791,NodePlus59.w14,CompactPlus3776.checked3790,CompactPlus3776.small3790,CompactPlus3776.nodes3790,NodePlus59.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus3776.p3791,GridPlus.atNode 3791,GridPlus.atNode 3792,NodePlus59.w15,CompactPlus3776.checked3791,CompactPlus3776.small3791,CompactPlus3776.nodes3791,NodePlus59.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus3792.p3792,GridPlus.atNode 3792,GridPlus.atNode 3793,NodePlus59.w16,CompactPlus3792.checked3792,CompactPlus3792.small3792,CompactPlus3792.nodes3792,NodePlus59.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus3792.p3793,GridPlus.atNode 3793,GridPlus.atNode 3794,NodePlus59.w17,CompactPlus3792.checked3793,CompactPlus3792.small3793,CompactPlus3792.nodes3793,NodePlus59.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus3792.p3794,GridPlus.atNode 3794,GridPlus.atNode 3795,NodePlus59.w18,CompactPlus3792.checked3794,CompactPlus3792.small3794,CompactPlus3792.nodes3794,NodePlus59.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus3792.p3795,GridPlus.atNode 3795,GridPlus.atNode 3796,NodePlus59.w19,CompactPlus3792.checked3795,CompactPlus3792.small3795,CompactPlus3792.nodes3795,NodePlus59.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus3792.p3796,GridPlus.atNode 3796,GridPlus.atNode 3797,NodePlus59.w20,CompactPlus3792.checked3796,CompactPlus3792.small3796,CompactPlus3792.nodes3796,NodePlus59.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus3792.p3797,GridPlus.atNode 3797,GridPlus.atNode 3798,NodePlus59.w21,CompactPlus3792.checked3797,CompactPlus3792.small3797,CompactPlus3792.nodes3797,NodePlus59.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus3792.p3798,GridPlus.atNode 3798,GridPlus.atNode 3799,NodePlus59.w22,CompactPlus3792.checked3798,CompactPlus3792.small3798,CompactPlus3792.nodes3798,NodePlus59.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus3792.p3799,GridPlus.atNode 3799,GridPlus.atNode 3800,NodePlus59.w23,CompactPlus3792.checked3799,CompactPlus3792.small3799,CompactPlus3792.nodes3799,NodePlus59.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus3792.p3800,GridPlus.atNode 3800,GridPlus.atNode 3801,NodePlus59.w24,CompactPlus3792.checked3800,CompactPlus3792.small3800,CompactPlus3792.nodes3800,NodePlus59.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus3792.p3801,GridPlus.atNode 3801,GridPlus.atNode 3802,NodePlus59.w25,CompactPlus3792.checked3801,CompactPlus3792.small3801,CompactPlus3792.nodes3801,NodePlus59.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus3792.p3802,GridPlus.atNode 3802,GridPlus.atNode 3803,NodePlus59.w26,CompactPlus3792.checked3802,CompactPlus3792.small3802,CompactPlus3792.nodes3802,NodePlus59.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus3792.p3803,GridPlus.atNode 3803,GridPlus.atNode 3804,NodePlus59.w27,CompactPlus3792.checked3803,CompactPlus3792.small3803,CompactPlus3792.nodes3803,NodePlus59.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus3792.p3804,GridPlus.atNode 3804,GridPlus.atNode 3805,NodePlus59.w28,CompactPlus3792.checked3804,CompactPlus3792.small3804,CompactPlus3792.nodes3804,NodePlus59.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus3792.p3805,GridPlus.atNode 3805,GridPlus.atNode 3806,NodePlus59.w29,CompactPlus3792.checked3805,CompactPlus3792.small3805,CompactPlus3792.nodes3805,NodePlus59.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus3792.p3806,GridPlus.atNode 3806,GridPlus.atNode 3807,NodePlus59.w30,CompactPlus3792.checked3806,CompactPlus3792.small3806,CompactPlus3792.nodes3806,NodePlus59.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus3792.p3807,GridPlus.atNode 3807,GridPlus.atNode 3808,NodePlus59.w31,CompactPlus3792.checked3807,CompactPlus3792.small3807,CompactPlus3792.nodes3807,NodePlus59.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus3808.p3808,GridPlus.atNode 3808,GridPlus.atNode 3809,NodePlus59.w32,CompactPlus3808.checked3808,CompactPlus3808.small3808,CompactPlus3808.nodes3808,NodePlus59.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus3808.p3809,GridPlus.atNode 3809,GridPlus.atNode 3810,NodePlus59.w33,CompactPlus3808.checked3809,CompactPlus3808.small3809,CompactPlus3808.nodes3809,NodePlus59.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus3808.p3810,GridPlus.atNode 3810,GridPlus.atNode 3811,NodePlus59.w34,CompactPlus3808.checked3810,CompactPlus3808.small3810,CompactPlus3808.nodes3810,NodePlus59.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus3808.p3811,GridPlus.atNode 3811,GridPlus.atNode 3812,NodePlus59.w35,CompactPlus3808.checked3811,CompactPlus3808.small3811,CompactPlus3808.nodes3811,NodePlus59.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus3808.p3812,GridPlus.atNode 3812,GridPlus.atNode 3813,NodePlus59.w36,CompactPlus3808.checked3812,CompactPlus3808.small3812,CompactPlus3808.nodes3812,NodePlus59.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus3808.p3813,GridPlus.atNode 3813,GridPlus.atNode 3814,NodePlus59.w37,CompactPlus3808.checked3813,CompactPlus3808.small3813,CompactPlus3808.nodes3813,NodePlus59.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus3808.p3814,GridPlus.atNode 3814,GridPlus.atNode 3815,NodePlus59.w38,CompactPlus3808.checked3814,CompactPlus3808.small3814,CompactPlus3808.nodes3814,NodePlus59.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus3808.p3815,GridPlus.atNode 3815,GridPlus.atNode 3816,NodePlus59.w39,CompactPlus3808.checked3815,CompactPlus3808.small3815,CompactPlus3808.nodes3815,NodePlus59.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus3808.p3816,GridPlus.atNode 3816,GridPlus.atNode 3817,NodePlus59.w40,CompactPlus3808.checked3816,CompactPlus3808.small3816,CompactPlus3808.nodes3816,NodePlus59.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus3808.p3817,GridPlus.atNode 3817,GridPlus.atNode 3818,NodePlus59.w41,CompactPlus3808.checked3817,CompactPlus3808.small3817,CompactPlus3808.nodes3817,NodePlus59.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus3808.p3818,GridPlus.atNode 3818,GridPlus.atNode 3819,NodePlus59.w42,CompactPlus3808.checked3818,CompactPlus3808.small3818,CompactPlus3808.nodes3818,NodePlus59.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus3808.p3819,GridPlus.atNode 3819,GridPlus.atNode 3820,NodePlus59.w43,CompactPlus3808.checked3819,CompactPlus3808.small3819,CompactPlus3808.nodes3819,NodePlus59.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus3808.p3820,GridPlus.atNode 3820,GridPlus.atNode 3821,NodePlus59.w44,CompactPlus3808.checked3820,CompactPlus3808.small3820,CompactPlus3808.nodes3820,NodePlus59.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus3808.p3821,GridPlus.atNode 3821,GridPlus.atNode 3822,NodePlus59.w45,CompactPlus3808.checked3821,CompactPlus3808.small3821,CompactPlus3808.nodes3821,NodePlus59.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus3808.p3822,GridPlus.atNode 3822,GridPlus.atNode 3823,NodePlus59.w46,CompactPlus3808.checked3822,CompactPlus3808.small3822,CompactPlus3808.nodes3822,NodePlus59.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus3808.p3823,GridPlus.atNode 3823,GridPlus.atNode 3824,NodePlus59.w47,CompactPlus3808.checked3823,CompactPlus3808.small3823,CompactPlus3808.nodes3823,NodePlus59.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus3824.p3824,GridPlus.atNode 3824,GridPlus.atNode 3825,NodePlus59.w48,CompactPlus3824.checked3824,CompactPlus3824.small3824,CompactPlus3824.nodes3824,NodePlus59.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus3824.p3825,GridPlus.atNode 3825,GridPlus.atNode 3826,NodePlus59.w49,CompactPlus3824.checked3825,CompactPlus3824.small3825,CompactPlus3824.nodes3825,NodePlus59.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus3824.p3826,GridPlus.atNode 3826,GridPlus.atNode 3827,NodePlus59.w50,CompactPlus3824.checked3826,CompactPlus3824.small3826,CompactPlus3824.nodes3826,NodePlus59.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus3824.p3827,GridPlus.atNode 3827,GridPlus.atNode 3828,NodePlus59.w51,CompactPlus3824.checked3827,CompactPlus3824.small3827,CompactPlus3824.nodes3827,NodePlus59.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus3824.p3828,GridPlus.atNode 3828,GridPlus.atNode 3829,NodePlus59.w52,CompactPlus3824.checked3828,CompactPlus3824.small3828,CompactPlus3824.nodes3828,NodePlus59.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus3824.p3829,GridPlus.atNode 3829,GridPlus.atNode 3830,NodePlus59.w53,CompactPlus3824.checked3829,CompactPlus3824.small3829,CompactPlus3824.nodes3829,NodePlus59.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus3824.p3830,GridPlus.atNode 3830,GridPlus.atNode 3831,NodePlus59.w54,CompactPlus3824.checked3830,CompactPlus3824.small3830,CompactPlus3824.nodes3830,NodePlus59.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus3824.p3831,GridPlus.atNode 3831,GridPlus.atNode 3832,NodePlus59.w55,CompactPlus3824.checked3831,CompactPlus3824.small3831,CompactPlus3824.nodes3831,NodePlus59.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus3824.p3832,GridPlus.atNode 3832,GridPlus.atNode 3833,NodePlus59.w56,CompactPlus3824.checked3832,CompactPlus3824.small3832,CompactPlus3824.nodes3832,NodePlus59.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus3824.p3833,GridPlus.atNode 3833,GridPlus.atNode 3834,NodePlus59.w57,CompactPlus3824.checked3833,CompactPlus3824.small3833,CompactPlus3824.nodes3833,NodePlus59.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus3824.p3834,GridPlus.atNode 3834,GridPlus.atNode 3835,NodePlus59.w58,CompactPlus3824.checked3834,CompactPlus3824.small3834,CompactPlus3824.nodes3834,NodePlus59.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus3824.p3835,GridPlus.atNode 3835,GridPlus.atNode 3836,NodePlus59.w59,CompactPlus3824.checked3835,CompactPlus3824.small3835,CompactPlus3824.nodes3835,NodePlus59.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus3824.p3836,GridPlus.atNode 3836,GridPlus.atNode 3837,NodePlus59.w60,CompactPlus3824.checked3836,CompactPlus3824.small3836,CompactPlus3824.nodes3836,NodePlus59.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus3824.p3837,GridPlus.atNode 3837,GridPlus.atNode 3838,NodePlus59.w61,CompactPlus3824.checked3837,CompactPlus3824.small3837,CompactPlus3824.nodes3837,NodePlus59.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus3824.p3838,GridPlus.atNode 3838,GridPlus.atNode 3839,NodePlus59.w62,CompactPlus3824.checked3838,CompactPlus3824.small3838,CompactPlus3824.nodes3838,NodePlus59.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus3824.p3839,GridPlus.atNode 3839,GridPlus.atNode 3840,NodePlus59.w63,CompactPlus3824.checked3839,CompactPlus3824.small3839,CompactPlus3824.nodes3839,NodePlus59.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (3776+j) ∧
    (atRow j).right=GridPlus.atNode (3776+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus59
