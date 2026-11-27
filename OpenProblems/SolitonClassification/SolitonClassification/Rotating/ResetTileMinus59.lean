import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus3776
import SolitonClassification.Rotating.ResetPackedMinus3792
import SolitonClassification.Rotating.ResetPackedMinus3808
import SolitonClassification.Rotating.ResetPackedMinus3824
namespace SolitonClassification.Rotating.DyadicReset.TileMinus59
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3776.p3776,GridMinus.atNode 3776,GridMinus.atNode 3777,NodeMinus59.w0,CompactMinus3776.checked3776,CompactMinus3776.small3776,CompactMinus3776.nodes3776,NodeMinus59.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3776.p3777,GridMinus.atNode 3777,GridMinus.atNode 3778,NodeMinus59.w1,CompactMinus3776.checked3777,CompactMinus3776.small3777,CompactMinus3776.nodes3777,NodeMinus59.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3776.p3778,GridMinus.atNode 3778,GridMinus.atNode 3779,NodeMinus59.w2,CompactMinus3776.checked3778,CompactMinus3776.small3778,CompactMinus3776.nodes3778,NodeMinus59.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3776.p3779,GridMinus.atNode 3779,GridMinus.atNode 3780,NodeMinus59.w3,CompactMinus3776.checked3779,CompactMinus3776.small3779,CompactMinus3776.nodes3779,NodeMinus59.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3776.p3780,GridMinus.atNode 3780,GridMinus.atNode 3781,NodeMinus59.w4,CompactMinus3776.checked3780,CompactMinus3776.small3780,CompactMinus3776.nodes3780,NodeMinus59.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3776.p3781,GridMinus.atNode 3781,GridMinus.atNode 3782,NodeMinus59.w5,CompactMinus3776.checked3781,CompactMinus3776.small3781,CompactMinus3776.nodes3781,NodeMinus59.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3776.p3782,GridMinus.atNode 3782,GridMinus.atNode 3783,NodeMinus59.w6,CompactMinus3776.checked3782,CompactMinus3776.small3782,CompactMinus3776.nodes3782,NodeMinus59.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3776.p3783,GridMinus.atNode 3783,GridMinus.atNode 3784,NodeMinus59.w7,CompactMinus3776.checked3783,CompactMinus3776.small3783,CompactMinus3776.nodes3783,NodeMinus59.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3776.p3784,GridMinus.atNode 3784,GridMinus.atNode 3785,NodeMinus59.w8,CompactMinus3776.checked3784,CompactMinus3776.small3784,CompactMinus3776.nodes3784,NodeMinus59.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3776.p3785,GridMinus.atNode 3785,GridMinus.atNode 3786,NodeMinus59.w9,CompactMinus3776.checked3785,CompactMinus3776.small3785,CompactMinus3776.nodes3785,NodeMinus59.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3776.p3786,GridMinus.atNode 3786,GridMinus.atNode 3787,NodeMinus59.w10,CompactMinus3776.checked3786,CompactMinus3776.small3786,CompactMinus3776.nodes3786,NodeMinus59.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3776.p3787,GridMinus.atNode 3787,GridMinus.atNode 3788,NodeMinus59.w11,CompactMinus3776.checked3787,CompactMinus3776.small3787,CompactMinus3776.nodes3787,NodeMinus59.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3776.p3788,GridMinus.atNode 3788,GridMinus.atNode 3789,NodeMinus59.w12,CompactMinus3776.checked3788,CompactMinus3776.small3788,CompactMinus3776.nodes3788,NodeMinus59.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3776.p3789,GridMinus.atNode 3789,GridMinus.atNode 3790,NodeMinus59.w13,CompactMinus3776.checked3789,CompactMinus3776.small3789,CompactMinus3776.nodes3789,NodeMinus59.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3776.p3790,GridMinus.atNode 3790,GridMinus.atNode 3791,NodeMinus59.w14,CompactMinus3776.checked3790,CompactMinus3776.small3790,CompactMinus3776.nodes3790,NodeMinus59.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3776.p3791,GridMinus.atNode 3791,GridMinus.atNode 3792,NodeMinus59.w15,CompactMinus3776.checked3791,CompactMinus3776.small3791,CompactMinus3776.nodes3791,NodeMinus59.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3792.p3792,GridMinus.atNode 3792,GridMinus.atNode 3793,NodeMinus59.w16,CompactMinus3792.checked3792,CompactMinus3792.small3792,CompactMinus3792.nodes3792,NodeMinus59.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3792.p3793,GridMinus.atNode 3793,GridMinus.atNode 3794,NodeMinus59.w17,CompactMinus3792.checked3793,CompactMinus3792.small3793,CompactMinus3792.nodes3793,NodeMinus59.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3792.p3794,GridMinus.atNode 3794,GridMinus.atNode 3795,NodeMinus59.w18,CompactMinus3792.checked3794,CompactMinus3792.small3794,CompactMinus3792.nodes3794,NodeMinus59.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3792.p3795,GridMinus.atNode 3795,GridMinus.atNode 3796,NodeMinus59.w19,CompactMinus3792.checked3795,CompactMinus3792.small3795,CompactMinus3792.nodes3795,NodeMinus59.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3792.p3796,GridMinus.atNode 3796,GridMinus.atNode 3797,NodeMinus59.w20,CompactMinus3792.checked3796,CompactMinus3792.small3796,CompactMinus3792.nodes3796,NodeMinus59.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3792.p3797,GridMinus.atNode 3797,GridMinus.atNode 3798,NodeMinus59.w21,CompactMinus3792.checked3797,CompactMinus3792.small3797,CompactMinus3792.nodes3797,NodeMinus59.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3792.p3798,GridMinus.atNode 3798,GridMinus.atNode 3799,NodeMinus59.w22,CompactMinus3792.checked3798,CompactMinus3792.small3798,CompactMinus3792.nodes3798,NodeMinus59.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3792.p3799,GridMinus.atNode 3799,GridMinus.atNode 3800,NodeMinus59.w23,CompactMinus3792.checked3799,CompactMinus3792.small3799,CompactMinus3792.nodes3799,NodeMinus59.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3792.p3800,GridMinus.atNode 3800,GridMinus.atNode 3801,NodeMinus59.w24,CompactMinus3792.checked3800,CompactMinus3792.small3800,CompactMinus3792.nodes3800,NodeMinus59.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3792.p3801,GridMinus.atNode 3801,GridMinus.atNode 3802,NodeMinus59.w25,CompactMinus3792.checked3801,CompactMinus3792.small3801,CompactMinus3792.nodes3801,NodeMinus59.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3792.p3802,GridMinus.atNode 3802,GridMinus.atNode 3803,NodeMinus59.w26,CompactMinus3792.checked3802,CompactMinus3792.small3802,CompactMinus3792.nodes3802,NodeMinus59.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3792.p3803,GridMinus.atNode 3803,GridMinus.atNode 3804,NodeMinus59.w27,CompactMinus3792.checked3803,CompactMinus3792.small3803,CompactMinus3792.nodes3803,NodeMinus59.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3792.p3804,GridMinus.atNode 3804,GridMinus.atNode 3805,NodeMinus59.w28,CompactMinus3792.checked3804,CompactMinus3792.small3804,CompactMinus3792.nodes3804,NodeMinus59.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3792.p3805,GridMinus.atNode 3805,GridMinus.atNode 3806,NodeMinus59.w29,CompactMinus3792.checked3805,CompactMinus3792.small3805,CompactMinus3792.nodes3805,NodeMinus59.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3792.p3806,GridMinus.atNode 3806,GridMinus.atNode 3807,NodeMinus59.w30,CompactMinus3792.checked3806,CompactMinus3792.small3806,CompactMinus3792.nodes3806,NodeMinus59.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3792.p3807,GridMinus.atNode 3807,GridMinus.atNode 3808,NodeMinus59.w31,CompactMinus3792.checked3807,CompactMinus3792.small3807,CompactMinus3792.nodes3807,NodeMinus59.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3808.p3808,GridMinus.atNode 3808,GridMinus.atNode 3809,NodeMinus59.w32,CompactMinus3808.checked3808,CompactMinus3808.small3808,CompactMinus3808.nodes3808,NodeMinus59.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3808.p3809,GridMinus.atNode 3809,GridMinus.atNode 3810,NodeMinus59.w33,CompactMinus3808.checked3809,CompactMinus3808.small3809,CompactMinus3808.nodes3809,NodeMinus59.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3808.p3810,GridMinus.atNode 3810,GridMinus.atNode 3811,NodeMinus59.w34,CompactMinus3808.checked3810,CompactMinus3808.small3810,CompactMinus3808.nodes3810,NodeMinus59.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3808.p3811,GridMinus.atNode 3811,GridMinus.atNode 3812,NodeMinus59.w35,CompactMinus3808.checked3811,CompactMinus3808.small3811,CompactMinus3808.nodes3811,NodeMinus59.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3808.p3812,GridMinus.atNode 3812,GridMinus.atNode 3813,NodeMinus59.w36,CompactMinus3808.checked3812,CompactMinus3808.small3812,CompactMinus3808.nodes3812,NodeMinus59.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3808.p3813,GridMinus.atNode 3813,GridMinus.atNode 3814,NodeMinus59.w37,CompactMinus3808.checked3813,CompactMinus3808.small3813,CompactMinus3808.nodes3813,NodeMinus59.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3808.p3814,GridMinus.atNode 3814,GridMinus.atNode 3815,NodeMinus59.w38,CompactMinus3808.checked3814,CompactMinus3808.small3814,CompactMinus3808.nodes3814,NodeMinus59.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3808.p3815,GridMinus.atNode 3815,GridMinus.atNode 3816,NodeMinus59.w39,CompactMinus3808.checked3815,CompactMinus3808.small3815,CompactMinus3808.nodes3815,NodeMinus59.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3808.p3816,GridMinus.atNode 3816,GridMinus.atNode 3817,NodeMinus59.w40,CompactMinus3808.checked3816,CompactMinus3808.small3816,CompactMinus3808.nodes3816,NodeMinus59.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3808.p3817,GridMinus.atNode 3817,GridMinus.atNode 3818,NodeMinus59.w41,CompactMinus3808.checked3817,CompactMinus3808.small3817,CompactMinus3808.nodes3817,NodeMinus59.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3808.p3818,GridMinus.atNode 3818,GridMinus.atNode 3819,NodeMinus59.w42,CompactMinus3808.checked3818,CompactMinus3808.small3818,CompactMinus3808.nodes3818,NodeMinus59.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3808.p3819,GridMinus.atNode 3819,GridMinus.atNode 3820,NodeMinus59.w43,CompactMinus3808.checked3819,CompactMinus3808.small3819,CompactMinus3808.nodes3819,NodeMinus59.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3808.p3820,GridMinus.atNode 3820,GridMinus.atNode 3821,NodeMinus59.w44,CompactMinus3808.checked3820,CompactMinus3808.small3820,CompactMinus3808.nodes3820,NodeMinus59.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3808.p3821,GridMinus.atNode 3821,GridMinus.atNode 3822,NodeMinus59.w45,CompactMinus3808.checked3821,CompactMinus3808.small3821,CompactMinus3808.nodes3821,NodeMinus59.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3808.p3822,GridMinus.atNode 3822,GridMinus.atNode 3823,NodeMinus59.w46,CompactMinus3808.checked3822,CompactMinus3808.small3822,CompactMinus3808.nodes3822,NodeMinus59.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3808.p3823,GridMinus.atNode 3823,GridMinus.atNode 3824,NodeMinus59.w47,CompactMinus3808.checked3823,CompactMinus3808.small3823,CompactMinus3808.nodes3823,NodeMinus59.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3824.p3824,GridMinus.atNode 3824,GridMinus.atNode 3825,NodeMinus59.w48,CompactMinus3824.checked3824,CompactMinus3824.small3824,CompactMinus3824.nodes3824,NodeMinus59.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3824.p3825,GridMinus.atNode 3825,GridMinus.atNode 3826,NodeMinus59.w49,CompactMinus3824.checked3825,CompactMinus3824.small3825,CompactMinus3824.nodes3825,NodeMinus59.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3824.p3826,GridMinus.atNode 3826,GridMinus.atNode 3827,NodeMinus59.w50,CompactMinus3824.checked3826,CompactMinus3824.small3826,CompactMinus3824.nodes3826,NodeMinus59.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3824.p3827,GridMinus.atNode 3827,GridMinus.atNode 3828,NodeMinus59.w51,CompactMinus3824.checked3827,CompactMinus3824.small3827,CompactMinus3824.nodes3827,NodeMinus59.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3824.p3828,GridMinus.atNode 3828,GridMinus.atNode 3829,NodeMinus59.w52,CompactMinus3824.checked3828,CompactMinus3824.small3828,CompactMinus3824.nodes3828,NodeMinus59.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3824.p3829,GridMinus.atNode 3829,GridMinus.atNode 3830,NodeMinus59.w53,CompactMinus3824.checked3829,CompactMinus3824.small3829,CompactMinus3824.nodes3829,NodeMinus59.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3824.p3830,GridMinus.atNode 3830,GridMinus.atNode 3831,NodeMinus59.w54,CompactMinus3824.checked3830,CompactMinus3824.small3830,CompactMinus3824.nodes3830,NodeMinus59.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3824.p3831,GridMinus.atNode 3831,GridMinus.atNode 3832,NodeMinus59.w55,CompactMinus3824.checked3831,CompactMinus3824.small3831,CompactMinus3824.nodes3831,NodeMinus59.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3824.p3832,GridMinus.atNode 3832,GridMinus.atNode 3833,NodeMinus59.w56,CompactMinus3824.checked3832,CompactMinus3824.small3832,CompactMinus3824.nodes3832,NodeMinus59.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3824.p3833,GridMinus.atNode 3833,GridMinus.atNode 3834,NodeMinus59.w57,CompactMinus3824.checked3833,CompactMinus3824.small3833,CompactMinus3824.nodes3833,NodeMinus59.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3824.p3834,GridMinus.atNode 3834,GridMinus.atNode 3835,NodeMinus59.w58,CompactMinus3824.checked3834,CompactMinus3824.small3834,CompactMinus3824.nodes3834,NodeMinus59.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3824.p3835,GridMinus.atNode 3835,GridMinus.atNode 3836,NodeMinus59.w59,CompactMinus3824.checked3835,CompactMinus3824.small3835,CompactMinus3824.nodes3835,NodeMinus59.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3824.p3836,GridMinus.atNode 3836,GridMinus.atNode 3837,NodeMinus59.w60,CompactMinus3824.checked3836,CompactMinus3824.small3836,CompactMinus3824.nodes3836,NodeMinus59.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3824.p3837,GridMinus.atNode 3837,GridMinus.atNode 3838,NodeMinus59.w61,CompactMinus3824.checked3837,CompactMinus3824.small3837,CompactMinus3824.nodes3837,NodeMinus59.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3824.p3838,GridMinus.atNode 3838,GridMinus.atNode 3839,NodeMinus59.w62,CompactMinus3824.checked3838,CompactMinus3824.small3838,CompactMinus3824.nodes3838,NodeMinus59.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3824.p3839,GridMinus.atNode 3839,GridMinus.atNode 3840,NodeMinus59.w63,CompactMinus3824.checked3839,CompactMinus3824.small3839,CompactMinus3824.nodes3839,NodeMinus59.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (3776+j) ∧
    (atRow j).right=GridMinus.atNode (3776+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus59
