import SolitonClassification.Rotating.ResetRows
import SolitonClassification.Rotating.ResetGridPlus
import SolitonClassification.Rotating.ResetPackedPlus3904
import SolitonClassification.Rotating.ResetPackedPlus3920
import SolitonClassification.Rotating.ResetPackedPlus3936
import SolitonClassification.Rotating.ResetPackedPlus3952
namespace SolitonClassification.Rotating.DyadicReset.TilePlus61
noncomputable section
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
def r0 : TapeRow Middle.hn :=
  ⟨CompactPlus3904.p3904,GridPlus.atNode 3904,GridPlus.atNode 3905,NodePlus61.w0,CompactPlus3904.checked3904,CompactPlus3904.small3904,CompactPlus3904.nodes3904,NodePlus61.bounds0⟩
def r1 : TapeRow Middle.hn :=
  ⟨CompactPlus3904.p3905,GridPlus.atNode 3905,GridPlus.atNode 3906,NodePlus61.w1,CompactPlus3904.checked3905,CompactPlus3904.small3905,CompactPlus3904.nodes3905,NodePlus61.bounds1⟩
def r2 : TapeRow Middle.hn :=
  ⟨CompactPlus3904.p3906,GridPlus.atNode 3906,GridPlus.atNode 3907,NodePlus61.w2,CompactPlus3904.checked3906,CompactPlus3904.small3906,CompactPlus3904.nodes3906,NodePlus61.bounds2⟩
def r3 : TapeRow Middle.hn :=
  ⟨CompactPlus3904.p3907,GridPlus.atNode 3907,GridPlus.atNode 3908,NodePlus61.w3,CompactPlus3904.checked3907,CompactPlus3904.small3907,CompactPlus3904.nodes3907,NodePlus61.bounds3⟩
def r4 : TapeRow Middle.hn :=
  ⟨CompactPlus3904.p3908,GridPlus.atNode 3908,GridPlus.atNode 3909,NodePlus61.w4,CompactPlus3904.checked3908,CompactPlus3904.small3908,CompactPlus3904.nodes3908,NodePlus61.bounds4⟩
def r5 : TapeRow Middle.hn :=
  ⟨CompactPlus3904.p3909,GridPlus.atNode 3909,GridPlus.atNode 3910,NodePlus61.w5,CompactPlus3904.checked3909,CompactPlus3904.small3909,CompactPlus3904.nodes3909,NodePlus61.bounds5⟩
def r6 : TapeRow Middle.hn :=
  ⟨CompactPlus3904.p3910,GridPlus.atNode 3910,GridPlus.atNode 3911,NodePlus61.w6,CompactPlus3904.checked3910,CompactPlus3904.small3910,CompactPlus3904.nodes3910,NodePlus61.bounds6⟩
def r7 : TapeRow Middle.hn :=
  ⟨CompactPlus3904.p3911,GridPlus.atNode 3911,GridPlus.atNode 3912,NodePlus61.w7,CompactPlus3904.checked3911,CompactPlus3904.small3911,CompactPlus3904.nodes3911,NodePlus61.bounds7⟩
def r8 : TapeRow Middle.hn :=
  ⟨CompactPlus3904.p3912,GridPlus.atNode 3912,GridPlus.atNode 3913,NodePlus61.w8,CompactPlus3904.checked3912,CompactPlus3904.small3912,CompactPlus3904.nodes3912,NodePlus61.bounds8⟩
def r9 : TapeRow Middle.hn :=
  ⟨CompactPlus3904.p3913,GridPlus.atNode 3913,GridPlus.atNode 3914,NodePlus61.w9,CompactPlus3904.checked3913,CompactPlus3904.small3913,CompactPlus3904.nodes3913,NodePlus61.bounds9⟩
def r10 : TapeRow Middle.hn :=
  ⟨CompactPlus3904.p3914,GridPlus.atNode 3914,GridPlus.atNode 3915,NodePlus61.w10,CompactPlus3904.checked3914,CompactPlus3904.small3914,CompactPlus3904.nodes3914,NodePlus61.bounds10⟩
def r11 : TapeRow Middle.hn :=
  ⟨CompactPlus3904.p3915,GridPlus.atNode 3915,GridPlus.atNode 3916,NodePlus61.w11,CompactPlus3904.checked3915,CompactPlus3904.small3915,CompactPlus3904.nodes3915,NodePlus61.bounds11⟩
def r12 : TapeRow Middle.hn :=
  ⟨CompactPlus3904.p3916,GridPlus.atNode 3916,GridPlus.atNode 3917,NodePlus61.w12,CompactPlus3904.checked3916,CompactPlus3904.small3916,CompactPlus3904.nodes3916,NodePlus61.bounds12⟩
def r13 : TapeRow Middle.hn :=
  ⟨CompactPlus3904.p3917,GridPlus.atNode 3917,GridPlus.atNode 3918,NodePlus61.w13,CompactPlus3904.checked3917,CompactPlus3904.small3917,CompactPlus3904.nodes3917,NodePlus61.bounds13⟩
def r14 : TapeRow Middle.hn :=
  ⟨CompactPlus3904.p3918,GridPlus.atNode 3918,GridPlus.atNode 3919,NodePlus61.w14,CompactPlus3904.checked3918,CompactPlus3904.small3918,CompactPlus3904.nodes3918,NodePlus61.bounds14⟩
def r15 : TapeRow Middle.hn :=
  ⟨CompactPlus3904.p3919,GridPlus.atNode 3919,GridPlus.atNode 3920,NodePlus61.w15,CompactPlus3904.checked3919,CompactPlus3904.small3919,CompactPlus3904.nodes3919,NodePlus61.bounds15⟩
def r16 : TapeRow Middle.hn :=
  ⟨CompactPlus3920.p3920,GridPlus.atNode 3920,GridPlus.atNode 3921,NodePlus61.w16,CompactPlus3920.checked3920,CompactPlus3920.small3920,CompactPlus3920.nodes3920,NodePlus61.bounds16⟩
def r17 : TapeRow Middle.hn :=
  ⟨CompactPlus3920.p3921,GridPlus.atNode 3921,GridPlus.atNode 3922,NodePlus61.w17,CompactPlus3920.checked3921,CompactPlus3920.small3921,CompactPlus3920.nodes3921,NodePlus61.bounds17⟩
def r18 : TapeRow Middle.hn :=
  ⟨CompactPlus3920.p3922,GridPlus.atNode 3922,GridPlus.atNode 3923,NodePlus61.w18,CompactPlus3920.checked3922,CompactPlus3920.small3922,CompactPlus3920.nodes3922,NodePlus61.bounds18⟩
def r19 : TapeRow Middle.hn :=
  ⟨CompactPlus3920.p3923,GridPlus.atNode 3923,GridPlus.atNode 3924,NodePlus61.w19,CompactPlus3920.checked3923,CompactPlus3920.small3923,CompactPlus3920.nodes3923,NodePlus61.bounds19⟩
def r20 : TapeRow Middle.hn :=
  ⟨CompactPlus3920.p3924,GridPlus.atNode 3924,GridPlus.atNode 3925,NodePlus61.w20,CompactPlus3920.checked3924,CompactPlus3920.small3924,CompactPlus3920.nodes3924,NodePlus61.bounds20⟩
def r21 : TapeRow Middle.hn :=
  ⟨CompactPlus3920.p3925,GridPlus.atNode 3925,GridPlus.atNode 3926,NodePlus61.w21,CompactPlus3920.checked3925,CompactPlus3920.small3925,CompactPlus3920.nodes3925,NodePlus61.bounds21⟩
def r22 : TapeRow Middle.hn :=
  ⟨CompactPlus3920.p3926,GridPlus.atNode 3926,GridPlus.atNode 3927,NodePlus61.w22,CompactPlus3920.checked3926,CompactPlus3920.small3926,CompactPlus3920.nodes3926,NodePlus61.bounds22⟩
def r23 : TapeRow Middle.hn :=
  ⟨CompactPlus3920.p3927,GridPlus.atNode 3927,GridPlus.atNode 3928,NodePlus61.w23,CompactPlus3920.checked3927,CompactPlus3920.small3927,CompactPlus3920.nodes3927,NodePlus61.bounds23⟩
def r24 : TapeRow Middle.hn :=
  ⟨CompactPlus3920.p3928,GridPlus.atNode 3928,GridPlus.atNode 3929,NodePlus61.w24,CompactPlus3920.checked3928,CompactPlus3920.small3928,CompactPlus3920.nodes3928,NodePlus61.bounds24⟩
def r25 : TapeRow Middle.hn :=
  ⟨CompactPlus3920.p3929,GridPlus.atNode 3929,GridPlus.atNode 3930,NodePlus61.w25,CompactPlus3920.checked3929,CompactPlus3920.small3929,CompactPlus3920.nodes3929,NodePlus61.bounds25⟩
def r26 : TapeRow Middle.hn :=
  ⟨CompactPlus3920.p3930,GridPlus.atNode 3930,GridPlus.atNode 3931,NodePlus61.w26,CompactPlus3920.checked3930,CompactPlus3920.small3930,CompactPlus3920.nodes3930,NodePlus61.bounds26⟩
def r27 : TapeRow Middle.hn :=
  ⟨CompactPlus3920.p3931,GridPlus.atNode 3931,GridPlus.atNode 3932,NodePlus61.w27,CompactPlus3920.checked3931,CompactPlus3920.small3931,CompactPlus3920.nodes3931,NodePlus61.bounds27⟩
def r28 : TapeRow Middle.hn :=
  ⟨CompactPlus3920.p3932,GridPlus.atNode 3932,GridPlus.atNode 3933,NodePlus61.w28,CompactPlus3920.checked3932,CompactPlus3920.small3932,CompactPlus3920.nodes3932,NodePlus61.bounds28⟩
def r29 : TapeRow Middle.hn :=
  ⟨CompactPlus3920.p3933,GridPlus.atNode 3933,GridPlus.atNode 3934,NodePlus61.w29,CompactPlus3920.checked3933,CompactPlus3920.small3933,CompactPlus3920.nodes3933,NodePlus61.bounds29⟩
def r30 : TapeRow Middle.hn :=
  ⟨CompactPlus3920.p3934,GridPlus.atNode 3934,GridPlus.atNode 3935,NodePlus61.w30,CompactPlus3920.checked3934,CompactPlus3920.small3934,CompactPlus3920.nodes3934,NodePlus61.bounds30⟩
def r31 : TapeRow Middle.hn :=
  ⟨CompactPlus3920.p3935,GridPlus.atNode 3935,GridPlus.atNode 3936,NodePlus61.w31,CompactPlus3920.checked3935,CompactPlus3920.small3935,CompactPlus3920.nodes3935,NodePlus61.bounds31⟩
def r32 : TapeRow Middle.hn :=
  ⟨CompactPlus3936.p3936,GridPlus.atNode 3936,GridPlus.atNode 3937,NodePlus61.w32,CompactPlus3936.checked3936,CompactPlus3936.small3936,CompactPlus3936.nodes3936,NodePlus61.bounds32⟩
def r33 : TapeRow Middle.hn :=
  ⟨CompactPlus3936.p3937,GridPlus.atNode 3937,GridPlus.atNode 3938,NodePlus61.w33,CompactPlus3936.checked3937,CompactPlus3936.small3937,CompactPlus3936.nodes3937,NodePlus61.bounds33⟩
def r34 : TapeRow Middle.hn :=
  ⟨CompactPlus3936.p3938,GridPlus.atNode 3938,GridPlus.atNode 3939,NodePlus61.w34,CompactPlus3936.checked3938,CompactPlus3936.small3938,CompactPlus3936.nodes3938,NodePlus61.bounds34⟩
def r35 : TapeRow Middle.hn :=
  ⟨CompactPlus3936.p3939,GridPlus.atNode 3939,GridPlus.atNode 3940,NodePlus61.w35,CompactPlus3936.checked3939,CompactPlus3936.small3939,CompactPlus3936.nodes3939,NodePlus61.bounds35⟩
def r36 : TapeRow Middle.hn :=
  ⟨CompactPlus3936.p3940,GridPlus.atNode 3940,GridPlus.atNode 3941,NodePlus61.w36,CompactPlus3936.checked3940,CompactPlus3936.small3940,CompactPlus3936.nodes3940,NodePlus61.bounds36⟩
def r37 : TapeRow Middle.hn :=
  ⟨CompactPlus3936.p3941,GridPlus.atNode 3941,GridPlus.atNode 3942,NodePlus61.w37,CompactPlus3936.checked3941,CompactPlus3936.small3941,CompactPlus3936.nodes3941,NodePlus61.bounds37⟩
def r38 : TapeRow Middle.hn :=
  ⟨CompactPlus3936.p3942,GridPlus.atNode 3942,GridPlus.atNode 3943,NodePlus61.w38,CompactPlus3936.checked3942,CompactPlus3936.small3942,CompactPlus3936.nodes3942,NodePlus61.bounds38⟩
def r39 : TapeRow Middle.hn :=
  ⟨CompactPlus3936.p3943,GridPlus.atNode 3943,GridPlus.atNode 3944,NodePlus61.w39,CompactPlus3936.checked3943,CompactPlus3936.small3943,CompactPlus3936.nodes3943,NodePlus61.bounds39⟩
def r40 : TapeRow Middle.hn :=
  ⟨CompactPlus3936.p3944,GridPlus.atNode 3944,GridPlus.atNode 3945,NodePlus61.w40,CompactPlus3936.checked3944,CompactPlus3936.small3944,CompactPlus3936.nodes3944,NodePlus61.bounds40⟩
def r41 : TapeRow Middle.hn :=
  ⟨CompactPlus3936.p3945,GridPlus.atNode 3945,GridPlus.atNode 3946,NodePlus61.w41,CompactPlus3936.checked3945,CompactPlus3936.small3945,CompactPlus3936.nodes3945,NodePlus61.bounds41⟩
def r42 : TapeRow Middle.hn :=
  ⟨CompactPlus3936.p3946,GridPlus.atNode 3946,GridPlus.atNode 3947,NodePlus61.w42,CompactPlus3936.checked3946,CompactPlus3936.small3946,CompactPlus3936.nodes3946,NodePlus61.bounds42⟩
def r43 : TapeRow Middle.hn :=
  ⟨CompactPlus3936.p3947,GridPlus.atNode 3947,GridPlus.atNode 3948,NodePlus61.w43,CompactPlus3936.checked3947,CompactPlus3936.small3947,CompactPlus3936.nodes3947,NodePlus61.bounds43⟩
def r44 : TapeRow Middle.hn :=
  ⟨CompactPlus3936.p3948,GridPlus.atNode 3948,GridPlus.atNode 3949,NodePlus61.w44,CompactPlus3936.checked3948,CompactPlus3936.small3948,CompactPlus3936.nodes3948,NodePlus61.bounds44⟩
def r45 : TapeRow Middle.hn :=
  ⟨CompactPlus3936.p3949,GridPlus.atNode 3949,GridPlus.atNode 3950,NodePlus61.w45,CompactPlus3936.checked3949,CompactPlus3936.small3949,CompactPlus3936.nodes3949,NodePlus61.bounds45⟩
def r46 : TapeRow Middle.hn :=
  ⟨CompactPlus3936.p3950,GridPlus.atNode 3950,GridPlus.atNode 3951,NodePlus61.w46,CompactPlus3936.checked3950,CompactPlus3936.small3950,CompactPlus3936.nodes3950,NodePlus61.bounds46⟩
def r47 : TapeRow Middle.hn :=
  ⟨CompactPlus3936.p3951,GridPlus.atNode 3951,GridPlus.atNode 3952,NodePlus61.w47,CompactPlus3936.checked3951,CompactPlus3936.small3951,CompactPlus3936.nodes3951,NodePlus61.bounds47⟩
def r48 : TapeRow Middle.hn :=
  ⟨CompactPlus3952.p3952,GridPlus.atNode 3952,GridPlus.atNode 3953,NodePlus61.w48,CompactPlus3952.checked3952,CompactPlus3952.small3952,CompactPlus3952.nodes3952,NodePlus61.bounds48⟩
def r49 : TapeRow Middle.hn :=
  ⟨CompactPlus3952.p3953,GridPlus.atNode 3953,GridPlus.atNode 3954,NodePlus61.w49,CompactPlus3952.checked3953,CompactPlus3952.small3953,CompactPlus3952.nodes3953,NodePlus61.bounds49⟩
def r50 : TapeRow Middle.hn :=
  ⟨CompactPlus3952.p3954,GridPlus.atNode 3954,GridPlus.atNode 3955,NodePlus61.w50,CompactPlus3952.checked3954,CompactPlus3952.small3954,CompactPlus3952.nodes3954,NodePlus61.bounds50⟩
def r51 : TapeRow Middle.hn :=
  ⟨CompactPlus3952.p3955,GridPlus.atNode 3955,GridPlus.atNode 3956,NodePlus61.w51,CompactPlus3952.checked3955,CompactPlus3952.small3955,CompactPlus3952.nodes3955,NodePlus61.bounds51⟩
def r52 : TapeRow Middle.hn :=
  ⟨CompactPlus3952.p3956,GridPlus.atNode 3956,GridPlus.atNode 3957,NodePlus61.w52,CompactPlus3952.checked3956,CompactPlus3952.small3956,CompactPlus3952.nodes3956,NodePlus61.bounds52⟩
def r53 : TapeRow Middle.hn :=
  ⟨CompactPlus3952.p3957,GridPlus.atNode 3957,GridPlus.atNode 3958,NodePlus61.w53,CompactPlus3952.checked3957,CompactPlus3952.small3957,CompactPlus3952.nodes3957,NodePlus61.bounds53⟩
def r54 : TapeRow Middle.hn :=
  ⟨CompactPlus3952.p3958,GridPlus.atNode 3958,GridPlus.atNode 3959,NodePlus61.w54,CompactPlus3952.checked3958,CompactPlus3952.small3958,CompactPlus3952.nodes3958,NodePlus61.bounds54⟩
def r55 : TapeRow Middle.hn :=
  ⟨CompactPlus3952.p3959,GridPlus.atNode 3959,GridPlus.atNode 3960,NodePlus61.w55,CompactPlus3952.checked3959,CompactPlus3952.small3959,CompactPlus3952.nodes3959,NodePlus61.bounds55⟩
def r56 : TapeRow Middle.hn :=
  ⟨CompactPlus3952.p3960,GridPlus.atNode 3960,GridPlus.atNode 3961,NodePlus61.w56,CompactPlus3952.checked3960,CompactPlus3952.small3960,CompactPlus3952.nodes3960,NodePlus61.bounds56⟩
def r57 : TapeRow Middle.hn :=
  ⟨CompactPlus3952.p3961,GridPlus.atNode 3961,GridPlus.atNode 3962,NodePlus61.w57,CompactPlus3952.checked3961,CompactPlus3952.small3961,CompactPlus3952.nodes3961,NodePlus61.bounds57⟩
def r58 : TapeRow Middle.hn :=
  ⟨CompactPlus3952.p3962,GridPlus.atNode 3962,GridPlus.atNode 3963,NodePlus61.w58,CompactPlus3952.checked3962,CompactPlus3952.small3962,CompactPlus3952.nodes3962,NodePlus61.bounds58⟩
def r59 : TapeRow Middle.hn :=
  ⟨CompactPlus3952.p3963,GridPlus.atNode 3963,GridPlus.atNode 3964,NodePlus61.w59,CompactPlus3952.checked3963,CompactPlus3952.small3963,CompactPlus3952.nodes3963,NodePlus61.bounds59⟩
def r60 : TapeRow Middle.hn :=
  ⟨CompactPlus3952.p3964,GridPlus.atNode 3964,GridPlus.atNode 3965,NodePlus61.w60,CompactPlus3952.checked3964,CompactPlus3952.small3964,CompactPlus3952.nodes3964,NodePlus61.bounds60⟩
def r61 : TapeRow Middle.hn :=
  ⟨CompactPlus3952.p3965,GridPlus.atNode 3965,GridPlus.atNode 3966,NodePlus61.w61,CompactPlus3952.checked3965,CompactPlus3952.small3965,CompactPlus3952.nodes3965,NodePlus61.bounds61⟩
def r62 : TapeRow Middle.hn :=
  ⟨CompactPlus3952.p3966,GridPlus.atNode 3966,GridPlus.atNode 3967,NodePlus61.w62,CompactPlus3952.checked3966,CompactPlus3952.small3966,CompactPlus3952.nodes3966,NodePlus61.bounds62⟩
def r63 : TapeRow Middle.hn :=
  ⟨CompactPlus3952.p3967,GridPlus.atNode 3967,GridPlus.atNode 3968,NodePlus61.w63,CompactPlus3952.checked3967,CompactPlus3952.small3967,CompactPlus3952.nodes3967,NodePlus61.bounds63⟩
def entries : Array (TapeRow Middle.hn) := #[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63]
def atRow (j : ℕ) := (entries[j]?).getD r0
theorem at_index (j : ℕ) (hj : j<64) : (atRow j).left=GridPlus.atNode (3904+j) ∧
    (atRow j).right=GridPlus.atNode (3904+j+1) := by interval_cases j <;> exact ⟨rfl,rfl⟩
end
end SolitonClassification.Rotating.DyadicReset.TilePlus61
