import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus3712
import SolitonClassification.Rotating.ResetPackedPlus3728
import SolitonClassification.Rotating.ResetPackedPlus3744
import SolitonClassification.Rotating.ResetPackedPlus3760
namespace SolitonClassification.Rotating.DyadicReset.TilePlus58
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus3712.p3712,GridPlus.atNode 3712,GridPlus.atNode 3713,NodePlus58.w0,CompactPlus3712.checked3712,CompactPlus3712.small3712,CompactPlus3712.nodes3712,NodePlus58.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus3712.p3713,GridPlus.atNode 3713,GridPlus.atNode 3714,NodePlus58.w1,CompactPlus3712.checked3713,CompactPlus3712.small3713,CompactPlus3712.nodes3713,NodePlus58.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus3712.p3714,GridPlus.atNode 3714,GridPlus.atNode 3715,NodePlus58.w2,CompactPlus3712.checked3714,CompactPlus3712.small3714,CompactPlus3712.nodes3714,NodePlus58.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus3712.p3715,GridPlus.atNode 3715,GridPlus.atNode 3716,NodePlus58.w3,CompactPlus3712.checked3715,CompactPlus3712.small3715,CompactPlus3712.nodes3715,NodePlus58.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus3712.p3716,GridPlus.atNode 3716,GridPlus.atNode 3717,NodePlus58.w4,CompactPlus3712.checked3716,CompactPlus3712.small3716,CompactPlus3712.nodes3716,NodePlus58.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus3712.p3717,GridPlus.atNode 3717,GridPlus.atNode 3718,NodePlus58.w5,CompactPlus3712.checked3717,CompactPlus3712.small3717,CompactPlus3712.nodes3717,NodePlus58.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus3712.p3718,GridPlus.atNode 3718,GridPlus.atNode 3719,NodePlus58.w6,CompactPlus3712.checked3718,CompactPlus3712.small3718,CompactPlus3712.nodes3718,NodePlus58.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus3712.p3719,GridPlus.atNode 3719,GridPlus.atNode 3720,NodePlus58.w7,CompactPlus3712.checked3719,CompactPlus3712.small3719,CompactPlus3712.nodes3719,NodePlus58.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus3712.p3720,GridPlus.atNode 3720,GridPlus.atNode 3721,NodePlus58.w8,CompactPlus3712.checked3720,CompactPlus3712.small3720,CompactPlus3712.nodes3720,NodePlus58.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus3712.p3721,GridPlus.atNode 3721,GridPlus.atNode 3722,NodePlus58.w9,CompactPlus3712.checked3721,CompactPlus3712.small3721,CompactPlus3712.nodes3721,NodePlus58.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus3712.p3722,GridPlus.atNode 3722,GridPlus.atNode 3723,NodePlus58.w10,CompactPlus3712.checked3722,CompactPlus3712.small3722,CompactPlus3712.nodes3722,NodePlus58.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus3712.p3723,GridPlus.atNode 3723,GridPlus.atNode 3724,NodePlus58.w11,CompactPlus3712.checked3723,CompactPlus3712.small3723,CompactPlus3712.nodes3723,NodePlus58.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus3712.p3724,GridPlus.atNode 3724,GridPlus.atNode 3725,NodePlus58.w12,CompactPlus3712.checked3724,CompactPlus3712.small3724,CompactPlus3712.nodes3724,NodePlus58.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus3712.p3725,GridPlus.atNode 3725,GridPlus.atNode 3726,NodePlus58.w13,CompactPlus3712.checked3725,CompactPlus3712.small3725,CompactPlus3712.nodes3725,NodePlus58.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus3712.p3726,GridPlus.atNode 3726,GridPlus.atNode 3727,NodePlus58.w14,CompactPlus3712.checked3726,CompactPlus3712.small3726,CompactPlus3712.nodes3726,NodePlus58.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus3712.p3727,GridPlus.atNode 3727,GridPlus.atNode 3728,NodePlus58.w15,CompactPlus3712.checked3727,CompactPlus3712.small3727,CompactPlus3712.nodes3727,NodePlus58.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus3728.p3728,GridPlus.atNode 3728,GridPlus.atNode 3729,NodePlus58.w16,CompactPlus3728.checked3728,CompactPlus3728.small3728,CompactPlus3728.nodes3728,NodePlus58.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus3728.p3729,GridPlus.atNode 3729,GridPlus.atNode 3730,NodePlus58.w17,CompactPlus3728.checked3729,CompactPlus3728.small3729,CompactPlus3728.nodes3729,NodePlus58.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus3728.p3730,GridPlus.atNode 3730,GridPlus.atNode 3731,NodePlus58.w18,CompactPlus3728.checked3730,CompactPlus3728.small3730,CompactPlus3728.nodes3730,NodePlus58.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus3728.p3731,GridPlus.atNode 3731,GridPlus.atNode 3732,NodePlus58.w19,CompactPlus3728.checked3731,CompactPlus3728.small3731,CompactPlus3728.nodes3731,NodePlus58.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus3728.p3732,GridPlus.atNode 3732,GridPlus.atNode 3733,NodePlus58.w20,CompactPlus3728.checked3732,CompactPlus3728.small3732,CompactPlus3728.nodes3732,NodePlus58.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus3728.p3733,GridPlus.atNode 3733,GridPlus.atNode 3734,NodePlus58.w21,CompactPlus3728.checked3733,CompactPlus3728.small3733,CompactPlus3728.nodes3733,NodePlus58.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus3728.p3734,GridPlus.atNode 3734,GridPlus.atNode 3735,NodePlus58.w22,CompactPlus3728.checked3734,CompactPlus3728.small3734,CompactPlus3728.nodes3734,NodePlus58.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus3728.p3735,GridPlus.atNode 3735,GridPlus.atNode 3736,NodePlus58.w23,CompactPlus3728.checked3735,CompactPlus3728.small3735,CompactPlus3728.nodes3735,NodePlus58.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus3728.p3736,GridPlus.atNode 3736,GridPlus.atNode 3737,NodePlus58.w24,CompactPlus3728.checked3736,CompactPlus3728.small3736,CompactPlus3728.nodes3736,NodePlus58.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus3728.p3737,GridPlus.atNode 3737,GridPlus.atNode 3738,NodePlus58.w25,CompactPlus3728.checked3737,CompactPlus3728.small3737,CompactPlus3728.nodes3737,NodePlus58.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus3728.p3738,GridPlus.atNode 3738,GridPlus.atNode 3739,NodePlus58.w26,CompactPlus3728.checked3738,CompactPlus3728.small3738,CompactPlus3728.nodes3738,NodePlus58.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus3728.p3739,GridPlus.atNode 3739,GridPlus.atNode 3740,NodePlus58.w27,CompactPlus3728.checked3739,CompactPlus3728.small3739,CompactPlus3728.nodes3739,NodePlus58.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus3728.p3740,GridPlus.atNode 3740,GridPlus.atNode 3741,NodePlus58.w28,CompactPlus3728.checked3740,CompactPlus3728.small3740,CompactPlus3728.nodes3740,NodePlus58.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus3728.p3741,GridPlus.atNode 3741,GridPlus.atNode 3742,NodePlus58.w29,CompactPlus3728.checked3741,CompactPlus3728.small3741,CompactPlus3728.nodes3741,NodePlus58.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus3728.p3742,GridPlus.atNode 3742,GridPlus.atNode 3743,NodePlus58.w30,CompactPlus3728.checked3742,CompactPlus3728.small3742,CompactPlus3728.nodes3742,NodePlus58.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus3728.p3743,GridPlus.atNode 3743,GridPlus.atNode 3744,NodePlus58.w31,CompactPlus3728.checked3743,CompactPlus3728.small3743,CompactPlus3728.nodes3743,NodePlus58.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus3744.p3744,GridPlus.atNode 3744,GridPlus.atNode 3745,NodePlus58.w32,CompactPlus3744.checked3744,CompactPlus3744.small3744,CompactPlus3744.nodes3744,NodePlus58.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus3744.p3745,GridPlus.atNode 3745,GridPlus.atNode 3746,NodePlus58.w33,CompactPlus3744.checked3745,CompactPlus3744.small3745,CompactPlus3744.nodes3745,NodePlus58.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus3744.p3746,GridPlus.atNode 3746,GridPlus.atNode 3747,NodePlus58.w34,CompactPlus3744.checked3746,CompactPlus3744.small3746,CompactPlus3744.nodes3746,NodePlus58.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus3744.p3747,GridPlus.atNode 3747,GridPlus.atNode 3748,NodePlus58.w35,CompactPlus3744.checked3747,CompactPlus3744.small3747,CompactPlus3744.nodes3747,NodePlus58.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus3744.p3748,GridPlus.atNode 3748,GridPlus.atNode 3749,NodePlus58.w36,CompactPlus3744.checked3748,CompactPlus3744.small3748,CompactPlus3744.nodes3748,NodePlus58.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus3744.p3749,GridPlus.atNode 3749,GridPlus.atNode 3750,NodePlus58.w37,CompactPlus3744.checked3749,CompactPlus3744.small3749,CompactPlus3744.nodes3749,NodePlus58.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus3744.p3750,GridPlus.atNode 3750,GridPlus.atNode 3751,NodePlus58.w38,CompactPlus3744.checked3750,CompactPlus3744.small3750,CompactPlus3744.nodes3750,NodePlus58.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus3744.p3751,GridPlus.atNode 3751,GridPlus.atNode 3752,NodePlus58.w39,CompactPlus3744.checked3751,CompactPlus3744.small3751,CompactPlus3744.nodes3751,NodePlus58.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus3744.p3752,GridPlus.atNode 3752,GridPlus.atNode 3753,NodePlus58.w40,CompactPlus3744.checked3752,CompactPlus3744.small3752,CompactPlus3744.nodes3752,NodePlus58.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus3744.p3753,GridPlus.atNode 3753,GridPlus.atNode 3754,NodePlus58.w41,CompactPlus3744.checked3753,CompactPlus3744.small3753,CompactPlus3744.nodes3753,NodePlus58.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus3744.p3754,GridPlus.atNode 3754,GridPlus.atNode 3755,NodePlus58.w42,CompactPlus3744.checked3754,CompactPlus3744.small3754,CompactPlus3744.nodes3754,NodePlus58.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus3744.p3755,GridPlus.atNode 3755,GridPlus.atNode 3756,NodePlus58.w43,CompactPlus3744.checked3755,CompactPlus3744.small3755,CompactPlus3744.nodes3755,NodePlus58.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus3744.p3756,GridPlus.atNode 3756,GridPlus.atNode 3757,NodePlus58.w44,CompactPlus3744.checked3756,CompactPlus3744.small3756,CompactPlus3744.nodes3756,NodePlus58.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus3744.p3757,GridPlus.atNode 3757,GridPlus.atNode 3758,NodePlus58.w45,CompactPlus3744.checked3757,CompactPlus3744.small3757,CompactPlus3744.nodes3757,NodePlus58.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus3744.p3758,GridPlus.atNode 3758,GridPlus.atNode 3759,NodePlus58.w46,CompactPlus3744.checked3758,CompactPlus3744.small3758,CompactPlus3744.nodes3758,NodePlus58.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus3744.p3759,GridPlus.atNode 3759,GridPlus.atNode 3760,NodePlus58.w47,CompactPlus3744.checked3759,CompactPlus3744.small3759,CompactPlus3744.nodes3759,NodePlus58.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus3760.p3760,GridPlus.atNode 3760,GridPlus.atNode 3761,NodePlus58.w48,CompactPlus3760.checked3760,CompactPlus3760.small3760,CompactPlus3760.nodes3760,NodePlus58.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus3760.p3761,GridPlus.atNode 3761,GridPlus.atNode 3762,NodePlus58.w49,CompactPlus3760.checked3761,CompactPlus3760.small3761,CompactPlus3760.nodes3761,NodePlus58.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus3760.p3762,GridPlus.atNode 3762,GridPlus.atNode 3763,NodePlus58.w50,CompactPlus3760.checked3762,CompactPlus3760.small3762,CompactPlus3760.nodes3762,NodePlus58.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus3760.p3763,GridPlus.atNode 3763,GridPlus.atNode 3764,NodePlus58.w51,CompactPlus3760.checked3763,CompactPlus3760.small3763,CompactPlus3760.nodes3763,NodePlus58.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus3760.p3764,GridPlus.atNode 3764,GridPlus.atNode 3765,NodePlus58.w52,CompactPlus3760.checked3764,CompactPlus3760.small3764,CompactPlus3760.nodes3764,NodePlus58.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus3760.p3765,GridPlus.atNode 3765,GridPlus.atNode 3766,NodePlus58.w53,CompactPlus3760.checked3765,CompactPlus3760.small3765,CompactPlus3760.nodes3765,NodePlus58.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus3760.p3766,GridPlus.atNode 3766,GridPlus.atNode 3767,NodePlus58.w54,CompactPlus3760.checked3766,CompactPlus3760.small3766,CompactPlus3760.nodes3766,NodePlus58.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus3760.p3767,GridPlus.atNode 3767,GridPlus.atNode 3768,NodePlus58.w55,CompactPlus3760.checked3767,CompactPlus3760.small3767,CompactPlus3760.nodes3767,NodePlus58.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus3760.p3768,GridPlus.atNode 3768,GridPlus.atNode 3769,NodePlus58.w56,CompactPlus3760.checked3768,CompactPlus3760.small3768,CompactPlus3760.nodes3768,NodePlus58.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus3760.p3769,GridPlus.atNode 3769,GridPlus.atNode 3770,NodePlus58.w57,CompactPlus3760.checked3769,CompactPlus3760.small3769,CompactPlus3760.nodes3769,NodePlus58.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus3760.p3770,GridPlus.atNode 3770,GridPlus.atNode 3771,NodePlus58.w58,CompactPlus3760.checked3770,CompactPlus3760.small3770,CompactPlus3760.nodes3770,NodePlus58.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus3760.p3771,GridPlus.atNode 3771,GridPlus.atNode 3772,NodePlus58.w59,CompactPlus3760.checked3771,CompactPlus3760.small3771,CompactPlus3760.nodes3771,NodePlus58.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus3760.p3772,GridPlus.atNode 3772,GridPlus.atNode 3773,NodePlus58.w60,CompactPlus3760.checked3772,CompactPlus3760.small3772,CompactPlus3760.nodes3772,NodePlus58.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus3760.p3773,GridPlus.atNode 3773,GridPlus.atNode 3774,NodePlus58.w61,CompactPlus3760.checked3773,CompactPlus3760.small3773,CompactPlus3760.nodes3773,NodePlus58.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus3760.p3774,GridPlus.atNode 3774,GridPlus.atNode 3775,NodePlus58.w62,CompactPlus3760.checked3774,CompactPlus3760.small3774,CompactPlus3760.nodes3774,NodePlus58.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus3760.p3775,GridPlus.atNode 3775,GridPlus.atNode 3776,NodePlus58.w63,CompactPlus3760.checked3775,CompactPlus3760.small3775,CompactPlus3760.nodes3775,NodePlus58.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (3712+j) ∧
    (atRow j).right=GridPlus.atNode (3712+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus58
