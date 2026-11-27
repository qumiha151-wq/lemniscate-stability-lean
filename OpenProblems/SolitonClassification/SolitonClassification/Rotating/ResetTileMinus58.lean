import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridMinus
import SolitonClassification.Rotating.ResetPackedMinus3712
import SolitonClassification.Rotating.ResetPackedMinus3728
import SolitonClassification.Rotating.ResetPackedMinus3744
import SolitonClassification.Rotating.ResetPackedMinus3760
namespace SolitonClassification.Rotating.DyadicReset.TileMinus58
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3712.p3712,GridMinus.atNode 3712,GridMinus.atNode 3713,NodeMinus58.w0,CompactMinus3712.checked3712,CompactMinus3712.small3712,CompactMinus3712.nodes3712,NodeMinus58.bounds0⟩
def r1 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3712.p3713,GridMinus.atNode 3713,GridMinus.atNode 3714,NodeMinus58.w1,CompactMinus3712.checked3713,CompactMinus3712.small3713,CompactMinus3712.nodes3713,NodeMinus58.bounds1⟩
def r2 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3712.p3714,GridMinus.atNode 3714,GridMinus.atNode 3715,NodeMinus58.w2,CompactMinus3712.checked3714,CompactMinus3712.small3714,CompactMinus3712.nodes3714,NodeMinus58.bounds2⟩
def r3 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3712.p3715,GridMinus.atNode 3715,GridMinus.atNode 3716,NodeMinus58.w3,CompactMinus3712.checked3715,CompactMinus3712.small3715,CompactMinus3712.nodes3715,NodeMinus58.bounds3⟩
def r4 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3712.p3716,GridMinus.atNode 3716,GridMinus.atNode 3717,NodeMinus58.w4,CompactMinus3712.checked3716,CompactMinus3712.small3716,CompactMinus3712.nodes3716,NodeMinus58.bounds4⟩
def r5 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3712.p3717,GridMinus.atNode 3717,GridMinus.atNode 3718,NodeMinus58.w5,CompactMinus3712.checked3717,CompactMinus3712.small3717,CompactMinus3712.nodes3717,NodeMinus58.bounds5⟩
def r6 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3712.p3718,GridMinus.atNode 3718,GridMinus.atNode 3719,NodeMinus58.w6,CompactMinus3712.checked3718,CompactMinus3712.small3718,CompactMinus3712.nodes3718,NodeMinus58.bounds6⟩
def r7 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3712.p3719,GridMinus.atNode 3719,GridMinus.atNode 3720,NodeMinus58.w7,CompactMinus3712.checked3719,CompactMinus3712.small3719,CompactMinus3712.nodes3719,NodeMinus58.bounds7⟩
def r8 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3712.p3720,GridMinus.atNode 3720,GridMinus.atNode 3721,NodeMinus58.w8,CompactMinus3712.checked3720,CompactMinus3712.small3720,CompactMinus3712.nodes3720,NodeMinus58.bounds8⟩
def r9 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3712.p3721,GridMinus.atNode 3721,GridMinus.atNode 3722,NodeMinus58.w9,CompactMinus3712.checked3721,CompactMinus3712.small3721,CompactMinus3712.nodes3721,NodeMinus58.bounds9⟩
def r10 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3712.p3722,GridMinus.atNode 3722,GridMinus.atNode 3723,NodeMinus58.w10,CompactMinus3712.checked3722,CompactMinus3712.small3722,CompactMinus3712.nodes3722,NodeMinus58.bounds10⟩
def r11 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3712.p3723,GridMinus.atNode 3723,GridMinus.atNode 3724,NodeMinus58.w11,CompactMinus3712.checked3723,CompactMinus3712.small3723,CompactMinus3712.nodes3723,NodeMinus58.bounds11⟩
def r12 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3712.p3724,GridMinus.atNode 3724,GridMinus.atNode 3725,NodeMinus58.w12,CompactMinus3712.checked3724,CompactMinus3712.small3724,CompactMinus3712.nodes3724,NodeMinus58.bounds12⟩
def r13 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3712.p3725,GridMinus.atNode 3725,GridMinus.atNode 3726,NodeMinus58.w13,CompactMinus3712.checked3725,CompactMinus3712.small3725,CompactMinus3712.nodes3725,NodeMinus58.bounds13⟩
def r14 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3712.p3726,GridMinus.atNode 3726,GridMinus.atNode 3727,NodeMinus58.w14,CompactMinus3712.checked3726,CompactMinus3712.small3726,CompactMinus3712.nodes3726,NodeMinus58.bounds14⟩
def r15 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3712.p3727,GridMinus.atNode 3727,GridMinus.atNode 3728,NodeMinus58.w15,CompactMinus3712.checked3727,CompactMinus3712.small3727,CompactMinus3712.nodes3727,NodeMinus58.bounds15⟩
def r16 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3728.p3728,GridMinus.atNode 3728,GridMinus.atNode 3729,NodeMinus58.w16,CompactMinus3728.checked3728,CompactMinus3728.small3728,CompactMinus3728.nodes3728,NodeMinus58.bounds16⟩
def r17 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3728.p3729,GridMinus.atNode 3729,GridMinus.atNode 3730,NodeMinus58.w17,CompactMinus3728.checked3729,CompactMinus3728.small3729,CompactMinus3728.nodes3729,NodeMinus58.bounds17⟩
def r18 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3728.p3730,GridMinus.atNode 3730,GridMinus.atNode 3731,NodeMinus58.w18,CompactMinus3728.checked3730,CompactMinus3728.small3730,CompactMinus3728.nodes3730,NodeMinus58.bounds18⟩
def r19 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3728.p3731,GridMinus.atNode 3731,GridMinus.atNode 3732,NodeMinus58.w19,CompactMinus3728.checked3731,CompactMinus3728.small3731,CompactMinus3728.nodes3731,NodeMinus58.bounds19⟩
def r20 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3728.p3732,GridMinus.atNode 3732,GridMinus.atNode 3733,NodeMinus58.w20,CompactMinus3728.checked3732,CompactMinus3728.small3732,CompactMinus3728.nodes3732,NodeMinus58.bounds20⟩
def r21 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3728.p3733,GridMinus.atNode 3733,GridMinus.atNode 3734,NodeMinus58.w21,CompactMinus3728.checked3733,CompactMinus3728.small3733,CompactMinus3728.nodes3733,NodeMinus58.bounds21⟩
def r22 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3728.p3734,GridMinus.atNode 3734,GridMinus.atNode 3735,NodeMinus58.w22,CompactMinus3728.checked3734,CompactMinus3728.small3734,CompactMinus3728.nodes3734,NodeMinus58.bounds22⟩
def r23 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3728.p3735,GridMinus.atNode 3735,GridMinus.atNode 3736,NodeMinus58.w23,CompactMinus3728.checked3735,CompactMinus3728.small3735,CompactMinus3728.nodes3735,NodeMinus58.bounds23⟩
def r24 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3728.p3736,GridMinus.atNode 3736,GridMinus.atNode 3737,NodeMinus58.w24,CompactMinus3728.checked3736,CompactMinus3728.small3736,CompactMinus3728.nodes3736,NodeMinus58.bounds24⟩
def r25 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3728.p3737,GridMinus.atNode 3737,GridMinus.atNode 3738,NodeMinus58.w25,CompactMinus3728.checked3737,CompactMinus3728.small3737,CompactMinus3728.nodes3737,NodeMinus58.bounds25⟩
def r26 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3728.p3738,GridMinus.atNode 3738,GridMinus.atNode 3739,NodeMinus58.w26,CompactMinus3728.checked3738,CompactMinus3728.small3738,CompactMinus3728.nodes3738,NodeMinus58.bounds26⟩
def r27 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3728.p3739,GridMinus.atNode 3739,GridMinus.atNode 3740,NodeMinus58.w27,CompactMinus3728.checked3739,CompactMinus3728.small3739,CompactMinus3728.nodes3739,NodeMinus58.bounds27⟩
def r28 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3728.p3740,GridMinus.atNode 3740,GridMinus.atNode 3741,NodeMinus58.w28,CompactMinus3728.checked3740,CompactMinus3728.small3740,CompactMinus3728.nodes3740,NodeMinus58.bounds28⟩
def r29 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3728.p3741,GridMinus.atNode 3741,GridMinus.atNode 3742,NodeMinus58.w29,CompactMinus3728.checked3741,CompactMinus3728.small3741,CompactMinus3728.nodes3741,NodeMinus58.bounds29⟩
def r30 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3728.p3742,GridMinus.atNode 3742,GridMinus.atNode 3743,NodeMinus58.w30,CompactMinus3728.checked3742,CompactMinus3728.small3742,CompactMinus3728.nodes3742,NodeMinus58.bounds30⟩
def r31 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3728.p3743,GridMinus.atNode 3743,GridMinus.atNode 3744,NodeMinus58.w31,CompactMinus3728.checked3743,CompactMinus3728.small3743,CompactMinus3728.nodes3743,NodeMinus58.bounds31⟩
def r32 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3744.p3744,GridMinus.atNode 3744,GridMinus.atNode 3745,NodeMinus58.w32,CompactMinus3744.checked3744,CompactMinus3744.small3744,CompactMinus3744.nodes3744,NodeMinus58.bounds32⟩
def r33 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3744.p3745,GridMinus.atNode 3745,GridMinus.atNode 3746,NodeMinus58.w33,CompactMinus3744.checked3745,CompactMinus3744.small3745,CompactMinus3744.nodes3745,NodeMinus58.bounds33⟩
def r34 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3744.p3746,GridMinus.atNode 3746,GridMinus.atNode 3747,NodeMinus58.w34,CompactMinus3744.checked3746,CompactMinus3744.small3746,CompactMinus3744.nodes3746,NodeMinus58.bounds34⟩
def r35 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3744.p3747,GridMinus.atNode 3747,GridMinus.atNode 3748,NodeMinus58.w35,CompactMinus3744.checked3747,CompactMinus3744.small3747,CompactMinus3744.nodes3747,NodeMinus58.bounds35⟩
def r36 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3744.p3748,GridMinus.atNode 3748,GridMinus.atNode 3749,NodeMinus58.w36,CompactMinus3744.checked3748,CompactMinus3744.small3748,CompactMinus3744.nodes3748,NodeMinus58.bounds36⟩
def r37 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3744.p3749,GridMinus.atNode 3749,GridMinus.atNode 3750,NodeMinus58.w37,CompactMinus3744.checked3749,CompactMinus3744.small3749,CompactMinus3744.nodes3749,NodeMinus58.bounds37⟩
def r38 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3744.p3750,GridMinus.atNode 3750,GridMinus.atNode 3751,NodeMinus58.w38,CompactMinus3744.checked3750,CompactMinus3744.small3750,CompactMinus3744.nodes3750,NodeMinus58.bounds38⟩
def r39 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3744.p3751,GridMinus.atNode 3751,GridMinus.atNode 3752,NodeMinus58.w39,CompactMinus3744.checked3751,CompactMinus3744.small3751,CompactMinus3744.nodes3751,NodeMinus58.bounds39⟩
def r40 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3744.p3752,GridMinus.atNode 3752,GridMinus.atNode 3753,NodeMinus58.w40,CompactMinus3744.checked3752,CompactMinus3744.small3752,CompactMinus3744.nodes3752,NodeMinus58.bounds40⟩
def r41 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3744.p3753,GridMinus.atNode 3753,GridMinus.atNode 3754,NodeMinus58.w41,CompactMinus3744.checked3753,CompactMinus3744.small3753,CompactMinus3744.nodes3753,NodeMinus58.bounds41⟩
def r42 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3744.p3754,GridMinus.atNode 3754,GridMinus.atNode 3755,NodeMinus58.w42,CompactMinus3744.checked3754,CompactMinus3744.small3754,CompactMinus3744.nodes3754,NodeMinus58.bounds42⟩
def r43 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3744.p3755,GridMinus.atNode 3755,GridMinus.atNode 3756,NodeMinus58.w43,CompactMinus3744.checked3755,CompactMinus3744.small3755,CompactMinus3744.nodes3755,NodeMinus58.bounds43⟩
def r44 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3744.p3756,GridMinus.atNode 3756,GridMinus.atNode 3757,NodeMinus58.w44,CompactMinus3744.checked3756,CompactMinus3744.small3756,CompactMinus3744.nodes3756,NodeMinus58.bounds44⟩
def r45 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3744.p3757,GridMinus.atNode 3757,GridMinus.atNode 3758,NodeMinus58.w45,CompactMinus3744.checked3757,CompactMinus3744.small3757,CompactMinus3744.nodes3757,NodeMinus58.bounds45⟩
def r46 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3744.p3758,GridMinus.atNode 3758,GridMinus.atNode 3759,NodeMinus58.w46,CompactMinus3744.checked3758,CompactMinus3744.small3758,CompactMinus3744.nodes3758,NodeMinus58.bounds46⟩
def r47 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3744.p3759,GridMinus.atNode 3759,GridMinus.atNode 3760,NodeMinus58.w47,CompactMinus3744.checked3759,CompactMinus3744.small3759,CompactMinus3744.nodes3759,NodeMinus58.bounds47⟩
def r48 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3760.p3760,GridMinus.atNode 3760,GridMinus.atNode 3761,NodeMinus58.w48,CompactMinus3760.checked3760,CompactMinus3760.small3760,CompactMinus3760.nodes3760,NodeMinus58.bounds48⟩
def r49 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3760.p3761,GridMinus.atNode 3761,GridMinus.atNode 3762,NodeMinus58.w49,CompactMinus3760.checked3761,CompactMinus3760.small3761,CompactMinus3760.nodes3761,NodeMinus58.bounds49⟩
def r50 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3760.p3762,GridMinus.atNode 3762,GridMinus.atNode 3763,NodeMinus58.w50,CompactMinus3760.checked3762,CompactMinus3760.small3762,CompactMinus3760.nodes3762,NodeMinus58.bounds50⟩
def r51 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3760.p3763,GridMinus.atNode 3763,GridMinus.atNode 3764,NodeMinus58.w51,CompactMinus3760.checked3763,CompactMinus3760.small3763,CompactMinus3760.nodes3763,NodeMinus58.bounds51⟩
def r52 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3760.p3764,GridMinus.atNode 3764,GridMinus.atNode 3765,NodeMinus58.w52,CompactMinus3760.checked3764,CompactMinus3760.small3764,CompactMinus3760.nodes3764,NodeMinus58.bounds52⟩
def r53 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3760.p3765,GridMinus.atNode 3765,GridMinus.atNode 3766,NodeMinus58.w53,CompactMinus3760.checked3765,CompactMinus3760.small3765,CompactMinus3760.nodes3765,NodeMinus58.bounds53⟩
def r54 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3760.p3766,GridMinus.atNode 3766,GridMinus.atNode 3767,NodeMinus58.w54,CompactMinus3760.checked3766,CompactMinus3760.small3766,CompactMinus3760.nodes3766,NodeMinus58.bounds54⟩
def r55 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3760.p3767,GridMinus.atNode 3767,GridMinus.atNode 3768,NodeMinus58.w55,CompactMinus3760.checked3767,CompactMinus3760.small3767,CompactMinus3760.nodes3767,NodeMinus58.bounds55⟩
def r56 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3760.p3768,GridMinus.atNode 3768,GridMinus.atNode 3769,NodeMinus58.w56,CompactMinus3760.checked3768,CompactMinus3760.small3768,CompactMinus3760.nodes3768,NodeMinus58.bounds56⟩
def r57 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3760.p3769,GridMinus.atNode 3769,GridMinus.atNode 3770,NodeMinus58.w57,CompactMinus3760.checked3769,CompactMinus3760.small3769,CompactMinus3760.nodes3769,NodeMinus58.bounds57⟩
def r58 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3760.p3770,GridMinus.atNode 3770,GridMinus.atNode 3771,NodeMinus58.w58,CompactMinus3760.checked3770,CompactMinus3760.small3770,CompactMinus3760.nodes3770,NodeMinus58.bounds58⟩
def r59 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3760.p3771,GridMinus.atNode 3771,GridMinus.atNode 3772,NodeMinus58.w59,CompactMinus3760.checked3771,CompactMinus3760.small3771,CompactMinus3760.nodes3771,NodeMinus58.bounds59⟩
def r60 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3760.p3772,GridMinus.atNode 3772,GridMinus.atNode 3773,NodeMinus58.w60,CompactMinus3760.checked3772,CompactMinus3760.small3772,CompactMinus3760.nodes3772,NodeMinus58.bounds60⟩
def r61 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3760.p3773,GridMinus.atNode 3773,GridMinus.atNode 3774,NodeMinus58.w61,CompactMinus3760.checked3773,CompactMinus3760.small3773,CompactMinus3760.nodes3773,NodeMinus58.bounds61⟩
def r62 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3760.p3774,GridMinus.atNode 3774,GridMinus.atNode 3775,NodeMinus58.w62,CompactMinus3760.checked3774,CompactMinus3760.small3774,CompactMinus3760.nodes3774,NodeMinus58.bounds62⟩
def r63 : TapeRow (-Middle.hn) :=
  ⟨CompactMinus3760.p3775,GridMinus.atNode 3775,GridMinus.atNode 3776,NodeMinus58.w63,CompactMinus3760.checked3775,CompactMinus3760.small3775,CompactMinus3760.nodes3775,NodeMinus58.bounds63⟩
def entries : Array (TapeRow (-Middle.hn)) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridMinus.atNode (3712+j) ∧
    (atRow j).right=GridMinus.atNode (3712+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TileMinus58
